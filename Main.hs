{-# LANGUAGE Rank2Types, ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall -fno-warn-name-shadowing #-}
module Main (main) where

import Control.Monad
import Control.Monad.IO.Class

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
--test_term = PrimOp Add [Value (Literal 1), Value (Literal 2)]
test_term = Let "x" (Value (Literal 1)) (Value (Literal 2))
--test_term = Let "x" (PrimOp Add [Value (Literal 1), Value (Literal 2)]) (Value (Lambda "y" (PrimOp Multiply [Var "y", Value (Literal 4)])) `App` "x")

main :: IO ()
main = do
    initializeNativeTarget
    
    let build_function = fmap snd $ runCompileM (compileTop test_term) (CE { symbolValues = M.empty }) ["float" ++ show (i :: Integer) | i <- [1..]]
    
    -- Use C API to build a LLVM Module containing our code
    m <- newModule
    (func_value, mappings) <- defineModule m (liftM2 (,) build_function getGlobalMappings)
    writeBitcodeToFile "output.bc" m
    
    -- JIT-compile our code
    prov <- createModuleProviderForExistingModule m
    func <- runEngineAccess $ do
        addModuleProvider prov
        addGlobalMappings mappings
        generateFunction func_value
    
    -- Run the compiled code
    putStrLn "Here we go:"
    func >>= print


-- We use this type to represent values in our system that are *either*
-- pointers to heap allocated closures/data *or* immediate Int32 values.
--
-- LLVM forbids void pointers, so we use the reccomended replacement:
type VoidPtr = Ptr Int8


data CompileEnv = CE {
    symbolValues :: M.Map Var (Value VoidPtr)
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


compileTop :: Term -> CompileM (Function (IO Int32))
compileTop e = do
    work <- compile e
    --printf <- liftCGM (newNamedFunction ExternalLinkage "printf" :: TFunction (Ptr Int8 -> VarArgs Int32))
    --format_string <- liftCGM (createStringNul "%d")
    
    liftCGM $ createFunction ExternalLinkage $ do
        -- For simplicity, we're going to assume that the code always returns an immediate integer
        value <- call work >>= ptrtoint :: CodeGenFunction Int32 (Value Int32)
        ret value :: CodeGenFunction Int32 Terminate
        
        --_nchars <- call printf format_string value
        --ret ()

compile :: Term -> CompileM (Function (IO VoidPtr))
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
         -> (CompileState -> Value VoidPtr -> CodeGenFunction VoidPtr r)
         -> CodeGenFunction VoidPtr r
compile' env s (Var x) k = compileVar env x >>= k s
compile' env s (Value v) k = case compileValue (M.keysSet (symbolValues env)) v of
    Immediate get_value_ptr -> get_value_ptr >>= k s
    HeapAllocated nwords poke -> do
        value_ptr <- arrayMalloc nwords
        s <- poke env s value_ptr
        bitcast value_ptr >>= k s
compile' env s (App e x) k = compile' env s e $ \s closure_ptr -> do
    arg_ptr <- compileVar env x
    
    fun_ptr_ptr <- bitcast closure_ptr :: CodeGenFunction VoidPtr (Value (Ptr (Ptr (VoidPtr -> VoidPtr -> IO VoidPtr))))
    fun_ptr <- load fun_ptr_ptr
    
    -- TODO: do I need to mark this as a tail call?
    call fun_ptr closure_ptr arg_ptr >>= k s
compile' env s (Case e alts) k = compile' env s e $ \s data_ptr -> do
    -- Retrieve the tag:
    tag_ptr <- bitcast data_ptr :: CodeGenFunction VoidPtr (Value (Ptr Int32))
    tag <- load tag_ptr
    
    -- Prepare the names of tail blocks, and the code that generates them
    join_block <- newBasicBlock
    panic_block <- newBasicBlock
    (blocks, define_blocks) <- fmap unzip $ forM alts $ \(dc, xs, e) -> do
        alt_block <- newBasicBlock
        let define_block s = do
              defineBasicBlock alt_block
              field_base_ptr <- bitcast data_ptr :: CodeGenFunction VoidPtr (Value (Ptr VoidPtr))
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
    compile' (env { symbolValues = M.insert x bound_ptr (symbolValues env) }) s e_body k
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
        value_ptr' <- bitcast value_ptr :: CodeGenFunction VoidPtr (Value VoidPtr)
        return ((x, value_ptr'), \env s -> maybe (return s) (\poke -> poke env s value_ptr) mb_poke :: CodeGenFunction VoidPtr CompileState)
    
    -- Create the extended environment with the new predictions, and actually initialize the values by using that environment
    let env' = env { symbolValues = M.fromList value_ptrs `M.union` symbolValues env }
    s <- forAccumLM_ s pokes (\s poke -> poke env' s)
    
    compile' env' s e_body k
compile' env s (PrimOp pop es) k = cpsBindN [TH (\s (k :: CompileState -> Value Int32 -> m r) -> compile' env s e (\s value_ptr -> ptrtoint value_ptr >>= k s)) | e <- es] s $ \s arg_ints -> do
    res_int <- case (pop, arg_ints) of
        (Add,      [i1, i2]) -> add i1 i2
        (Subtract, [i1, i2]) -> sub i1 i2
        (Multiply, [i1, i2]) -> mul i1 i2
        _ -> error "Bad primitive operation arity"
    inttoptr res_int >>= k s
compile' env s (Weaken x e) k = compile' (env { symbolValues = M.delete x (symbolValues env) }) s e k
compile' env s (Delay e) k = error "TODO: unimplemented" env s e k

compileVar :: CompileEnv -> Var -> CodeGenFunction VoidPtr (Value VoidPtr)
compileVar env x = case M.lookup x (symbolValues env) of
    Nothing        -> error $ "Unbound variable " ++ show x
    Just value_ptr -> return value_ptr

data ValueBuilder = Immediate (CodeGenFunction VoidPtr (Value VoidPtr))
                  | HeapAllocated Word32 (CompileEnv -> CompileState -> Value (Ptr VoidPtr) -> CodeGenFunction VoidPtr CompileState)

compileValue :: S.Set Var -> Val -> ValueBuilder
compileValue avails v = case v of
    -- Do not allocate space: we will pack Int32s into pointers
    -- NB: this code assumes Int32s fit into pointers! Probably safe, but...
    Literal l  -> Immediate $ inttoptr (valueOf l)
    -- Allocate space for one pointer per data item, and one pointer for the tag
    Data dc xs -> HeapAllocated (1 + genericLength xs) $ \env s data_ptr -> do
        -- Poke in the tag
        tag_ptr <- bitcast data_ptr :: CodeGenFunction VoidPtr (Value (Ptr Int32))
        store (valueOf (dataConTag dc)) tag_ptr
    
        -- Poke in the data
        forM_ (xs `zip` [1..]) $ \(x, offset) -> do
            field_ptr <- getElementPtr data_ptr (offset :: Int32, ())
            value_ptr <- compileVar env x
            store value_ptr field_ptr
    
        return s
    -- Allocate space for one pointer per closure variable, and one pointer for the code
    Lambda x e -> HeapAllocated (1 + fromIntegral (S.size avails_used)) $ \env s closure_ptr -> do
        let (name:names) = functionNameSupply s
            (closed_value_ptrs, get_closure_value_ptrs) = unzip $ flip map ([1..] `zip` M.toList (symbolValues env `restrict` avails_used)) $
                                                        \(offset, (x, value_ptr)) -> let get_value_ptr closure_ptr = do
                                                                                            field_ptr <- getElementPtr closure_ptr (offset :: Int32, ())
                                                                                            load field_ptr
                                                                                     in ((offset, value_ptr), (x, get_value_ptr))
        
        -- Poke in the code
        fun_ptr_ptr <- bitcast closure_ptr :: CodeGenFunction VoidPtr (Function (Ptr (VoidPtr -> VoidPtr -> IO VoidPtr)))
        fun_ptr <- externFunction name
        store fun_ptr fun_ptr_ptr
        
        -- Poke in the closure variables
        forM_ closed_value_ptrs $ \(offset, value_ptr) -> do
            field_ptr <- getElementPtr closure_ptr (offset, ())
            store value_ptr field_ptr
        
        -- Pend the definition of the code for function referened by that closure
        let define_function s = fmap (\(s, _fun_ptr :: Function (Ptr VoidPtr -> VoidPtr -> IO VoidPtr)) -> s) $ tunnelIO2 (createNamedFunction ExternalLinkage name) $ \closure_ptr arg_ptr -> do
                closure_value_ptrs <- forM get_closure_value_ptrs $ \(x, get_value_ptr) -> fmap ((,) x) $ get_value_ptr closure_ptr
                compile' (env { symbolValues = M.insert x arg_ptr (M.fromList closure_value_ptrs) }) s e $ \s value_ptr -> fmap ((,) s) (ret value_ptr)
        return (s { functionNameSupply = names, pendingFunctions = define_function : pendingFunctions s })
      where avails_used = S.delete x (termFreeVars avails e)


-- This is a proof-of-concept function used to show that (thanks to Weaken) we can still do the
-- useful optimisation of closing over only those things that may be touched in the future.
termFreeVars :: S.Set Var -> Term -> S.Set Var
termFreeVars worst_fvs e = term e
  where
    term e = case e of
      Var x -> S.singleton x
      Value v -> value v
      App e x -> S.insert x (term e)
      Case e alts -> term e `S.union` S.unions [term e S.\\ S.fromList xs | (_, xs, e) <- alts]
      LetRec xvs e -> (term e `S.union` S.unions (map value vs)) S.\\ S.fromList xs
        where (xs, vs) = unzip xvs
      Let x e1 e2 -> term e1 `S.union` S.delete x (term e2)
      PrimOp _ es -> S.unions (map term es)
      Weaken x e -> S.delete x (term e)
      Delay _ -> worst_fvs
    
    value v = case v of
      Lambda x e -> S.delete x (term e)
      Data _ xs  -> S.fromList xs
      Literal _  -> S.empty


restrict :: Ord k => M.Map k v -> S.Set k -> M.Map k v
restrict m s = M.filterWithKey (\x _ -> x `S.notMember` s) m

{-
mapAccumLM :: (Monad m) => (acc -> x -> m (acc, y)) -> acc -> [x] -> m (acc, [y])
mapAccumLM _ s []     = return (s, [])
mapAccumLM f s (x:xs) = do
     (s', y)  <- f s x
     (s'',ys) <- mapAccumLM f s' xs
     return (s'',y:ys)
-}

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
