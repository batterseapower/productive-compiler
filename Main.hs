{-# LANGUAGE Rank2Types, ScopedTypeVariables #-}
module Main (main) where

import Control.Monad
import Control.Monad.IO.Class

import Data.Char
import Data.Int
import Data.Word
import Data.List
import Data.IORef

import qualified Data.Map as M
import qualified Data.Set as S

import Foreign.Ptr

import LLVM.Core
import LLVM.ExecutionEngine


type Var = String

type Literal = Int32

data DataCon = DC { dataConName :: String, dataConTag :: Int32 }

data PrimOp = Add | Subtract | Multiply

-- A strict functional language
data Term = Var Var
          | Value Val
          | App Term Var
          | Case Term [(DataCon, [Var], Term)]
          | LetRec [(Var, Val)] Term
          | Let Var Term Term
          | PrimOp PrimOp [Term]
          | Weaken Var Term           -- Used to "forget" certain variables so we can keep closure size down
          | Delay Term                -- Introduces code that returns control to the compiler

data Val = Lambda Var Term
         | Data DataCon [Var]
         | Literal Literal

test_term :: Term
--test_term = Value (Lambda "x" (Var "x"))
test_term = PrimOp Add [Value (Literal 1), Value (Literal 2)]

main :: IO ()
main = do
    initializeNativeTarget
    f <- simpleFunction $ fmap snd $ runCompileM (compileTop test_term) (CE { symbolValues = M.empty }) ["float" ++ show i | i <- [1..]]
    f

data CompileEnv = CE {
    symbolValues :: M.Map Var (Value (Ptr ()))
  }

data CompileState = CS {
    pendingFunctions :: [CompileState -> CodeGenModule CompileState],
    functionNameSupply :: [String]
  }

newtype CompileM a = CM { unCM :: CompileEnv -> CompileState -> CodeGenModule (CompileState, a) }

runCompileM :: CompileM a -> CompileEnv -> [String] -> CodeGenModule ([String], a)
runCompileM cm env names = do
    (s, x) <- unCM cm env (CS { pendingFunctions = [], functionNameSupply = names })
    names <- discharge_pending s
    return (names, x)
  where
    discharge_pending s = case pendingFunctions s of
      []       -> return (functionNameSupply s)
      (cf:cfs) -> cf (s { pendingFunctions = cfs }) >>= discharge_pending

instance Functor CompileM where
    fmap = liftM

instance Monad CompileM where
    return x = CM $ \_ s -> return (s, x)
    mx >>= fxmy = CM $ \e s -> unCM mx e s >>= \(s, x) -> unCM (fxmy x) e s

liftCGM :: CodeGenModule a -> CompileM a
liftCGM cgm = CM $ \_ s -> fmap ((,) s) cgm


compileTop :: Term -> CompileM (Function (IO ()))
compileTop e = do
    work <- compile e
    putchar <- liftCGM (newNamedFunction ExternalLinkage "putchar" :: TFunction (Int32 -> IO Int32))
    
    liftCGM $ createFunction ExternalLinkage $ do
        _ptr <- call work
        _err <- call putchar (valueOf (fromIntegral (ord 'A')))
        ret ()

compile :: Term -> CompileM (Function (IO (Ptr ())))
compile e = CM $ \env s -> tunnelIO (createFunction ExternalLinkage) $ compile' env s e (\s value_ptr -> fmap ((,) s) (ret value_ptr))

tunnelIO :: (MonadIO m, MonadIO n)
         => (m a -> n b)
         -> m (c, a)
         -> n (c, b)
tunnelIO control arg = do
    -- Urgh, have to resort to tunneling through IORef to get the new State out
    s_ref <- liftIO $ newIORef (error "tunnelIO: unfilled IORef")
    fun <- control $ do
        (s, res) <- arg
        liftIO $ writeIORef s_ref s
        return res
    s <- liftIO $ readIORef s_ref
    return (s, fun)

tunnelIO2 :: (MonadIO m, MonadIO n)
          => ((arg1 -> arg2 -> m a) -> n b)
          -> (arg1 -> arg2 -> m (c, a))
          -> n (c, b)
tunnelIO2 control arg = do
    -- Urgh, have to resort to tunneling through IORef to get the new State out
    s_ref <- liftIO $ newIORef (error "tunnelIO: unfilled IORef")
    fun <- control $ \arg1 arg2 -> do
        (s, res) <- arg arg1 arg2
        liftIO $ writeIORef s_ref s
        return res
    s <- liftIO $ readIORef s_ref
    return (s, fun)

compile' :: CompileEnv -> CompileState -> Term
         -> (CompileState -> Value (Ptr ()) -> CodeGenFunction (Ptr ()) r)
         -> CodeGenFunction (Ptr ()) r
compile' env s (Var x) k = compileVar env x >>= k s
compile' env s (Value v) k = case compileValue (M.keysSet (symbolValues env)) v of
    Immediate get_value_ptr -> get_value_ptr >>= k s
    HeapAllocated nwords poke -> do
        value_ptr <- arrayMalloc nwords
        s <- poke env s value_ptr
        bitcast value_ptr >>= k s
compile' env s (App e x) k = compile' env s e $ \s closure_ptr -> do
    arg_ptr <- compileVar env x
    
    fun_ptr_ptr <- bitcast closure_ptr :: CodeGenFunction (Ptr ()) (Function (Ptr (Ptr () -> Ptr () -> IO (Ptr ()))))
    fun_ptr <- load fun_ptr_ptr
    
    call fun_ptr closure_ptr arg_ptr >>= k s
compile' env s (Case e alts) k = compile' env s e $ \s data_ptr -> do
    -- Retrieve the tag:
    tag_ptr <- bitcast data_ptr :: CodeGenFunction (Ptr ()) (Value (Ptr Int32))
    tag <- load tag_ptr
    
    -- Prepare the names of tail blocks, and the code that generates them
    join_block <- newBasicBlock
    panic_block <- newBasicBlock
    (blocks, define_blocks) <- fmap unzip $ forM alts $ \(dc, xs, e) -> do
        alt_block <- newBasicBlock
        let define_block s = do
              defineBasicBlock alt_block
              field_base_ptr <- bitcast data_ptr :: CodeGenFunction (Ptr ()) (Value (Ptr (Ptr ())))
              env <- forAccumLM_ env (xs `zip` [1..]) $ \env (x, offset) -> do
                  field_ptr <- getElementPtr field_base_ptr (offset :: Int32, ())
                  value_ptr <- load field_ptr
                  return (env { symbolValues = M.insert x value_ptr (symbolValues env) })
              (s, result_ptr) <- compile' env s e $ \s result_ptr -> br join_block >> return (s, result_ptr)
              return (s, (result_ptr, alt_block))
        return ((constOf (dataConTag dc), alt_block), define_block)
    
    -- Jump into appropriate tail code:
    switch tag panic_block blocks
    
    -- Define tail code
    (s, phi_data) <- accumLM s define_blocks
    defineBasicBlock panic_block
    unreachable
    defineBasicBlock join_block
    phi phi_data >>= k s
compile' env s (Let x e_bound e_body) k = compile' env s e_bound $ \s bound_ptr -> do
    compile' (env { symbolValues = M.insert x bound_ptr (symbolValues env) }) s e_bound k
compile' env s (LetRec xvs e_body) k = do
    -- Decide how each value will be allocated
    let avails = S.fromList (map fst xvs) `S.union` M.keysSet (symbolValues env)
        (nwords, get_value_ptrs_pokes) = forAccumL 0 xvs $ \nwords_total (x, v) -> case compileValue avails v of
                                                                     Immediate get_value_ptr   -> (nwords_total,          (x, \_         -> get_value_ptr >>= bitcast,                  Nothing))
                                                                     HeapAllocated nwords poke -> (nwords_total + nwords, (x, \block_ptr -> getElementPtr block_ptr (nwords_total, ()), Just poke))
    
    -- Allocate enough memory for all the values to fit in
    block_ptr <- arrayMalloc nwords
    -- We can predict the values each variable has before we actually intialize them. This is essential to tie the knot.
    (value_ptrs, pokes) <- fmap unzip $ forM get_value_ptrs_pokes $ \(x, get_value_ptr, mb_poke) -> do
        value_ptr <- get_value_ptr block_ptr
        value_ptr' <- bitcast value_ptr :: CodeGenFunction (Ptr ()) (Value (Ptr ()))
        return ((x, value_ptr'), \env s -> maybe (return s) (\poke -> poke env s value_ptr) mb_poke :: CodeGenFunction (Ptr ()) CompileState)
    
    -- Create the extended environment with the new predictions, and actually initialize the values by using that environment
    let env' = env { symbolValues = M.fromList value_ptrs `M.union` symbolValues env }
    s <- forAccumLM_ s pokes (\s poke -> poke env' s)
    
    compile' env' s e_body k
compile' env s (PrimOp pop es) k = cpsBindN [TH (\s (k :: CompileState -> Value Int32 -> m r) -> compile' env s e (\s value_ptr -> bitcast value_ptr >>= k s)) | e <- es] s $ \s arg_ints -> do
    res_int <- case (pop, arg_ints) of
        (Add,      [i1, i2]) -> add i1 i2
        (Subtract, [i1, i2]) -> sub i1 i2
        (Multiply, [i1, i2]) -> mul i1 i2
        _ -> error "Bad primitive operation arity"
    bitcast res_int >>= k s
compile' env s (Weaken x e) k = compile' (env { symbolValues = M.delete x (symbolValues env) }) s e k
compile' env s (Delay e) k = error "TODO: unimplemented"

compileVar :: CompileEnv -> Var -> CodeGenFunction (Ptr ()) (Value (Ptr ()))
compileVar env x = case M.lookup x (symbolValues env) of
    Nothing        -> error $ "Unbound variable " ++ show x
    Just value_ptr -> return value_ptr

data ValueBuilder = Immediate (CodeGenFunction (Ptr ()) (Value (Ptr ())))
                  | HeapAllocated Word32 (CompileEnv -> CompileState -> Value (Ptr (Ptr ())) -> CodeGenFunction (Ptr ()) CompileState)

compileValue :: S.Set Var -> Val -> ValueBuilder
compileValue avails v = case v of
    -- Do not allocate space: we will pack Int32s into pointers
    -- NB: this code assumes Int32s fit into pointers! Probably safe, but...
    Literal l  -> Immediate $ bitcast (valueOf l)
    -- Allocate space for one pointer per data item, and one pointer for the tag
    Data dc xs -> HeapAllocated (1 + genericLength xs) $ \env s data_ptr -> do
        -- Poke in the tag
        tag_ptr <- bitcast data_ptr :: CodeGenFunction (Ptr ()) (Value (Ptr Int32))
        store (valueOf (dataConTag dc)) tag_ptr
    
        -- Poke in the data
        forM (xs `zip` [1..]) $ \(x, offset) -> do
            field_ptr <- getElementPtr data_ptr (offset :: Int32, ())
            value_ptr <- compileVar env x
            store value_ptr field_ptr
    
        return s
    -- Allocate space for one pointer per closure variable, and one pointer for the code
    Lambda x e -> HeapAllocated (1 + fromIntegral (S.size avails)) $ \env s closure_ptr -> do
        let (name:names) = functionNameSupply s
            (closed_value_ptrs, get_closure_value_ptrs) = unzip $ flip map ([1..] `zip` M.toList (symbolValues env)) $
                                                        \(offset, (x, value_ptr)) -> let get_value_ptr closure_ptr = do
                                                                                            field_ptr <- getElementPtr closure_ptr (offset :: Int32, ())
                                                                                            load field_ptr
                                                                                     in ((offset, value_ptr), (x, get_value_ptr))
        
        -- Poke in the code
        fun_ptr_ptr <- bitcast closure_ptr :: CodeGenFunction (Ptr ()) (Function (Ptr (Ptr () -> Ptr () -> IO (Ptr ()))))
        fun_ptr <- externFunction name
        store fun_ptr fun_ptr_ptr
        
        -- Poke in the closure variables
        forM closed_value_ptrs $ \(offset, value_ptr) -> do
            field_ptr <- getElementPtr closure_ptr (offset, ())
            store value_ptr field_ptr
        
        -- Pend the definition of the code for function referened by that closure
        let define_function s = fmap (\(s, fun_ptr :: Function (Ptr (Ptr ()) -> Ptr () -> IO (Ptr ()))) -> s) $ tunnelIO2 (createNamedFunction ExternalLinkage name) $ \closure_ptr arg_ptr -> do
                closure_value_ptrs <- forM get_closure_value_ptrs $ \(x, get_value_ptr) -> fmap ((,) x) $ get_value_ptr closure_ptr
                compile' (env { symbolValues = M.insert x arg_ptr (M.fromList closure_value_ptrs) }) s e $ \s value_ptr -> fmap ((,) s) (ret value_ptr)
        return (s { functionNameSupply = names, pendingFunctions = define_function : pendingFunctions s })


-- TODO: use this to trim closure size
-- termFreeVars :: Term -> S.Set Var -> S.Set Var
-- termFreeVars (Var x) _ = S.singleton x
-- termFreeVars 


mapAccumLM :: (Monad m) => (acc -> x -> m (acc, y)) -> acc -> [x] -> m (acc, [y])
mapAccumLM _ s []     = return (s, [])
mapAccumLM f s (x:xs) = do
     (s', y)  <- f s x
     (s'',ys) <- mapAccumLM f s' xs
     return (s'',y:ys)

accumLM :: (Monad m) => acc -> [acc -> m (acc, y)] -> m (acc, [y])
accumLM s []     = return (s, [])
accumLM s (f:fs) = do
     (s', y)  <- f s
     (s'',ys) <- accumLM s' fs
     return (s'',y:ys)

-- Impredicative types do not seem to work too well (I can't get the call site to type-check),
-- so I'm working around the issue with this small wrapper:
newtype TypeHack s a m = TH { unTH :: forall r. s -> (s -> a -> m r) -> m r }

cpsBindN :: [TypeHack s a m]
         -> s
         -> (s -> [a] -> m r)
         -> m r
cpsBindN []     s k = k s []
cpsBindN (r:rs) s k = unTH r s $ \s x -> cpsBindN rs s $ \s xs -> k s (x:xs)

forAccumLM_ :: Monad m => acc -> [a] -> (acc -> a -> m acc) -> m acc
forAccumLM_ acc []     _ = return acc
forAccumLM_ acc (x:xs) f = do
    acc <- f acc x
    forAccumLM_ acc xs f

forAccumL :: acc -> [a] -> (acc -> a -> (acc, b)) -> (acc, [b])
forAccumL acc []     _ = (acc, [])
forAccumL acc (x:xs) f = case f acc x of (acc, y) -> case forAccumL acc xs f of (acc, ys) -> (acc, y:ys)
