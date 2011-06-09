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

import System.Directory (doesFileExist)
import System.IO (fixIO)

import Foreign.Ptr

import LLVM.Core
import LLVM.ExecutionEngine


type Var = String

type Literal = Int32

data DataCon = DC { dataConName :: String, dataConTag :: Int32 }

trueDataCon, falseDataCon :: DataCon
falseDataCon = DC "False" 0
trueDataCon = DC "True" 1

nothingDataCon, justDataCon :: DataCon
nothingDataCon = DC "Nothing" 0
justDataCon = DC "Just" 1

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
-- Simple arithmetic:
test_term = PrimOp Add [Value (Literal 1), Value (Literal 2)]
-- Test that exposed "let" miscompilation:
--test_term = Let "x" (Value (Literal 1)) (Value (Literal 2))
-- Simple case branches:
--test_term = Case (Value (Data trueDataCon [])) [(trueDataCon, [], Value (Literal 1)), (falseDataCon, [], Value (Literal 2))]
-- Complex case branches:
--test_term = Let "x" (Value (Literal 5)) $ Case (Value (Data justDataCon ["x"])) [(nothingDataCon, [], Value (Literal 1)), (justDataCon, ["y"], Var "y")]
-- FIXME below this line
-- Simple function use. Does not need to reference closure:
--test_term = Let "x" (PrimOp Add [Value (Literal 1), Value (Literal 2)]) (Value (Lambda "y" (PrimOp Multiply [Var "y", Value (Literal 4)])) `App` "x")
-- Complex function use. Needs to reference closure:
--test_term = Let "x" (PrimOp Add [Value (Literal 1), Value (Literal 2)]) (Let "four" (Value (Literal 4)) (Value (Lambda "y" (PrimOp Multiply [Var "y", Var "four"])) `App` "x"))
-- Trivial delay
--test_term = Delay (Value (Literal 1))

main :: IO ()
main = do
    initializeNativeTarget
    
    let build_function = runCompileM (compileTop test_term) (CE { symbolValues = M.empty })
    
    {-
    -- Build a LLVM Module containing our code
    m <- newModule
    (func_value, mappings) <- defineModule m (liftM2 (,) build_function getGlobalMappings)
    writeBitcodeToFile "output.bc" m
    
    -- JIT-compile our code
    prov <- createModuleProviderForExistingModule m
    func <- runEngineAccess $ do
        addModuleProvider prov
        addGlobalMappings mappings
        generateFunction func_value
    -}
    
    (poke_func_ptr, global_ptr) <- simpleFunction' $ do
        global <- createNamedGlobal False ExternalLinkage "dummy_constant" (constOf (10 :: Int32)) :: CodeGenModule (Global Int32)
        poke_func <- createNamedFunction ExternalLinkage "the_poker" $ do
            x <- load global
            y <- add x (1 :: Int32)
            store y global
            ret y
        return (liftM2 (,) (getPointerToFunction poke_func) (getPointerToFunction global))
    
    peek_func <- simpleFunction' $ do
        --global <- newNamedGlobal False ExternalLinkage "dummy_constant" :: CodeGenModule (Global Int32)
        
        --poker <- newNamedFunction ExternalLinkage "the_poker" :: CodeGenModule (Function (IO Int32))
        fmap generateFunction $ createFunction InternalLinkage $ do
            --poker <- staticFunction poke_func_ptr :: CodeGenFunction Int32 (Function (IO Int32))
            --x <- call poker
            global <- staticGlobal False (castFunPtrToPtr global_ptr) :: CodeGenFunction Int32 (Global Int32)
            x <- load global
            ret x
    
    let poke_func = mkIOInt32 poke_func_ptr
    
    (poke_func :: IO Int32) >>= print -- 11
    (poke_func :: IO Int32) >>= print -- 12
    (peek_func :: IO Int32) >>= print -- 12
    
    func <- simpleFunction' $ do
        fmap generateFunction build_function
    
    -- Run the compiled code
    putStrLn "Here we go:"
    func >>= print


simpleFunction' :: CodeGenModule (EngineAccess b) -> IO b
simpleFunction' bld = do
    m <- newModule
    (act, mappings) <- defineModule m (liftM2 (,) bld getGlobalMappings)
    
    -- Write code:
    let go n = do
            let fp = "output." ++ show n ++ ".bc"
            bad <- doesFileExist fp
            if bad then go (n + 1) else writeBitcodeToFile fp m
    go (0 :: Integer)
    
    prov <- createModuleProviderForExistingModule m
    runEngineAccess $ do
        addModuleProvider prov
        addGlobalMappings mappings
        act


-- We use this type to represent values in our system that are *either*
-- pointers to heap allocated closures/data *or* immediate Int32 values.
--
-- LLVM forbids void pointers, so we use the reccomended replacement:
type VoidPtr = Ptr Int8


data CompileEnv = CE {
    symbolValues :: M.Map Var (Value VoidPtr)
  }

type CompileState = ()

newtype CompileM a = CM { unCM :: CompileEnv -> CompileState -> CodeGenModule (CompileState, a) }

runCompileM :: CompileM a -> CompileEnv -> CodeGenModule a
runCompileM cm env = fmap snd (unCM cm env ())

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
    
    liftCGM $ createFunction InternalLinkage $ do
        -- For simplicity, we're going to assume that the code always returns an immediate integer
        value <- call work >>= ptrtoint :: CodeGenFunction Int32 (Value Int32)
        ret value :: CodeGenFunction Int32 Terminate
        
        --_nchars <- call printf format_string value
        --ret ()

compile :: Term -> CompileM (Function (IO VoidPtr))
compile e = CM $ \env s -> tunnelIO (createFunction InternalLinkage) $ compile' env s e (\s value_ptr -> fmap (const s) (ret value_ptr))

tunnelIO :: (MonadIO m, MonadIO n)
         => (m () -> n b)
         -> m c
         -> n (c, b)
tunnelIO control arg = do
    -- Urgh, have to resort to tunneling through IORef to get the new State out
    s_ref <- liftIO $ newIORef (error "tunnelIO: unfilled IORef")
    fun <- control $ do
        s <- arg
        liftIO $ writeIORef s_ref s
    s <- liftIO $ readIORef s_ref
    return (s, fun)

tunnelIO2 :: (MonadIO m, MonadIO n)
          => ((arg1 -> arg2 -> m ()) -> n b)
          -> (arg1 -> arg2 -> m c)
          -> n (c, b)
tunnelIO2 control arg = do
    -- Urgh, have to resort to tunneling through IORef to get the new State out
    s_ref <- liftIO $ newIORef (error "tunnelIO: unfilled IORef")
    fun <- control $ \arg1 arg2 -> do
        s <- arg arg1 arg2
        liftIO $ writeIORef s_ref s
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
compile' env s (Delay e) k = do
    -- Create a block of memory we can use to marshal our lexical environment around
    block_ptr <- arrayAlloca (fromIntegral (M.size (symbolValues env)) :: Word32) :: CodeGenFunction VoidPtr (Value (Ptr VoidPtr))
    get_block_value_ptrs <- forM ([0..] `zip` M.toList (symbolValues env)) $ \(offset, (x, value_ptr)) -> do
        field_ptr <- getElementPtr block_ptr (offset :: Int32, ())
        store value_ptr field_ptr
        return $ \block_ptr -> do
            field_ptr <- getElementPtr block_ptr (offset, ())
            fmap ((,) x) $ load field_ptr
    
    -- We transfer control to the function pointer stored in the global with this name
    let trampoline_global_name = "foo_name" -- FIXME: fresh name
    
    -- Create Haskell trampoline that will be invoked when we first need to compile this
    reenter_compiler_ptr <- liftIO $ fixIO $ \reenter_compiler_ptr -> wrapDelay $ \block_ptr -> do
        -- Build a Module containing the replacement code and fixup code that transfers
        -- control to the replacement code right now
        fixup_func <- simpleFunction' $ do
            replacement_func_value <- createFunction InternalLinkage $ \(block_ptr :: Value (Ptr VoidPtr)) -> do
                -- FIXME: in the future I may need a different CompileState here
                value_ptrs <- mapM ($ block_ptr) get_block_value_ptrs
                _s <- compile' (CE { symbolValues = M.fromList value_ptrs }) s e (\s value_ptr -> fmap (const s) (ret value_ptr))
                return ()
            
            trampoline_global <- newNamedGlobal False ExternalLinkage trampoline_global_name :: CodeGenModule (Global (Ptr (Ptr VoidPtr -> IO VoidPtr)))
            fmap generateFunction $ createFunction InternalLinkage $ \block_ptr -> do
                -- Make sure that next time we execute this Delay we jump right to the replacement
                store replacement_func_value trampoline_global
                -- Call the replacement code right now to get the work done
                call replacement_func_value block_ptr >>= ret
        
        -- Do the fixup
        freeHaskellFunPtr reenter_compiler_ptr -- TODO: I probably shouldn't free this function while it is still running!
        fixup_func block_ptr
    
    -- Transfer control
    trampoline_global <- liftCodeGenModule $ createNamedGlobal False ExternalLinkage trampoline_global_name (constOf (castFunPtrToPtr reenter_compiler_ptr))
    trampoline_ptr <- load trampoline_global
    call trampoline_ptr block_ptr >>= k s

foreign import ccall "wrapper"
    wrapDelay :: (Ptr VoidPtr -> IO VoidPtr) -> IO (FunPtr (Ptr VoidPtr -> IO VoidPtr))

foreign import ccall "dynamic" 
    mkIOInt32 :: FunPtr (IO Int32) -> IO Int32

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
        let (closed_value_ptrs, get_closure_value_ptrs) = unzip $ flip map ([1..] `zip` M.toList (symbolValues env `restrict` avails_used)) $
                                                        \(offset, (x, value_ptr)) -> let get_value_ptr closure_ptr = do
                                                                                            field_ptr <- getElementPtr closure_ptr (offset :: Int32, ())
                                                                                            load field_ptr
                                                                                     in ((offset, value_ptr), (x, get_value_ptr))
        
        -- Define the function corresponding to the lambda body
        (s, fun_ptr) <- liftCodeGenModule $ tunnelIO2 (createFunction InternalLinkage) $ \closure_ptr arg_ptr -> do
            closure_value_ptrs <- forM get_closure_value_ptrs $ \(x, get_value_ptr) -> fmap ((,) x) $ get_value_ptr closure_ptr
            compile' (env { symbolValues = M.insert x arg_ptr (M.fromList closure_value_ptrs) }) s e $ \s value_ptr -> fmap (const s) (ret value_ptr)
        
        -- Poke in the code
        fun_ptr_ptr <- bitcast closure_ptr :: CodeGenFunction VoidPtr (Function (Ptr (Ptr VoidPtr -> VoidPtr -> IO VoidPtr)))
        store fun_ptr fun_ptr_ptr
        
        -- Poke in the closure variables
        forM_ closed_value_ptrs $ \(offset, value_ptr) -> do
            field_ptr <- getElementPtr closure_ptr (offset, ())
            store value_ptr field_ptr
        
        return s
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
restrict m s = M.filterWithKey (\x _ -> x `S.member` s) m

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
