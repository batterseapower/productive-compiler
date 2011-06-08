{-# LANGUAGE Rank2Types, ScopedTypeVariables #-}
module Main (main) where

import Control.Monad

import Data.Char
import Data.Int
import Data.Word
import Data.List

import Foreign.Ptr

import qualified Data.Map as M

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
    f <- simpleFunction $ unCM (compileTop test_term) (CE { symbolValues = M.empty })
    f

data CompileEnv = CE {
    symbolValues    :: M.Map Var (CodeGenFunction (Ptr ()) (Value (Ptr ())))
  }

newtype CompileM a = CM { unCM :: CompileEnv -> CodeGenModule a }

instance Functor CompileM where
    fmap = liftM

instance Monad CompileM where
    return x = CM $ \_ -> return x
    mx >>= fxmy = CM $ \e -> unCM mx e >>= \x -> unCM (fxmy x) e

liftCGM :: CodeGenModule a -> CompileM a
liftCGM cgm = CM $ \_ -> cgm


compileTop :: Term -> CompileM (Function (IO ()))
compileTop e = do
    work <- compile e
    putchar <- liftCGM (newNamedFunction ExternalLinkage "putchar" :: TFunction (Int32 -> IO Int32))
    
    liftCGM $ createFunction ExternalLinkage $ do
        _ptr <- call work
        _err <- call putchar (valueOf (fromIntegral (ord 'A')))
        ret ()

compile :: Term -> CompileM (Function (IO (Ptr ())))
compile e = CM $ \env -> createFunction ExternalLinkage $ compile' env e ret

-- NB: this code assumes Int32s fit into pointers! Probably safe, but...
compile' :: CompileEnv -> Term
         -> (Value (Ptr ()) -> CodeGenFunction (Ptr ()) r)
         -> CodeGenFunction (Ptr ()) r
compile' env (Var x) k = compileVar env x >>= k
compile' env (Value v) k = compileValue env v >>= k
compile' env (App e x) k = compile' env e $ \closure_ptr -> do
    arg_ptr <- compileVar env x
    
    fun_ptr_ptr <- bitcast closure_ptr :: CodeGenFunction (Ptr ()) (Value (Ptr (Ptr (Ptr () -> Ptr () -> IO (Ptr ())))))
    fun_ptr <- load fun_ptr_ptr
    
    call fun_ptr closure_ptr arg_ptr >>= k
compile' env (Case e alts) k = compile' env e $ \data_ptr -> do
    -- Retrieve the tag:
    tag_ptr <- bitcast data_ptr :: CodeGenFunction (Ptr ()) (Value (Ptr Int32))
    tag <- load tag_ptr
    
    -- Prepare the names of tail blocks, and the code that generates them
    join_block <- newBasicBlock
    panic_block <- newBasicBlock
    (blocks, define_blocks) <- fmap unzip $ forM alts $ \(dc, xs, e) -> do
        alt_block <- newBasicBlock
        let define_block = do
              defineBasicBlock alt_block
              field_base_ptr <- bitcast data_ptr :: CodeGenFunction (Ptr ()) (Value (Ptr (Ptr ())))
              env <- foldM (\env (x, offset) -> do {
                    field_ptr <- getElementPtr field_base_ptr (offset :: Int32, ());
                    value_ptr <- load field_ptr;
                    return (env { symbolValues = M.insert x (return value_ptr) (symbolValues env) })
                  }) env (xs `zip` [1..])
              result_ptr <- compile' env e $ \result_ptr -> br join_block >> return result_ptr
              return (result_ptr, alt_block)
        return ((constOf (dataConTag dc), alt_block), define_block)
    
    -- Jump into appropriate tail code:
    switch tag panic_block blocks
    
    -- Define tail code
    phi_data <- sequence define_blocks
    defineBasicBlock panic_block
    unreachable
    defineBasicBlock join_block
    phi phi_data >>= k
compile' env (Let x e_bound e_body) k = compile' env e_bound $ \bound_ptr -> do
    compile' (env { symbolValues = M.insert x (return bound_ptr) (symbolValues env) }) e_bound k
compile' env (LetRec xvs e_body) k = do
    -- FIXME: this does not work properly
    (env, xvs) <- mapAccumLM (\env (x, v) -> do {
                delay_cell_ptr <- alloca :: CodeGenFunction (Ptr ()) (Value (Ptr (Ptr ())));
                return (env { symbolValues = M.insert x (load delay_cell_ptr) (symbolValues env) }, (delay_cell_ptr, v))
              }) env xvs
    
    forM_ xvs $ \(delay_cell_ptr, v) -> do
        value_ptr <- compileValue env v
        store value_ptr delay_cell_ptr
    
    compile' env e_body k
compile' env (PrimOp pop es) k = cpsBindN [TH (\(k :: Value Int32 -> m r) -> compile' env e (\value_ptr -> bitcast value_ptr >>= k)) | e <- es] $ \arg_values -> do
    res_value <- case (pop, arg_values) of
        (Add,      [i1, i2]) -> add i1 i2
        (Subtract, [i1, i2]) -> sub i1 i2
        (Multiply, [i1, i2]) -> mul i1 i2
        _ -> error "Bad primitive operation arity"
    bitcast res_value >>= k
compile' env (Weaken x e) k = compile' (env { symbolValues = M.delete x (symbolValues env) }) e k
compile' env (Delay e) k = error "TODO: unimplemented"

compileVar :: CompileEnv -> Var -> CodeGenFunction (Ptr ()) (Value (Ptr ()))
compileVar env x = case M.lookup x (symbolValues env) of
    Nothing        -> error $ "Unbound variable " ++ show x
    Just get_value -> get_value

compileValue :: CompileEnv -> Val -> CodeGenFunction (Ptr ()) (Value (Ptr ()))
compileValue env v = case v of
    Literal l  -> bitcast (valueOf l)
    Data dc xs -> do
        -- Allocate space for one pointer per data item, and one pointer for the tag
        data_ptr <- arrayMalloc (1 + genericLength xs :: Word32) :: CodeGenFunction (Ptr ()) (Value (Ptr (Ptr ())))
    
        -- Poke in the tag
        tag_ptr <- bitcast data_ptr :: CodeGenFunction (Ptr ()) (Value (Ptr Int32))
        store (valueOf (dataConTag dc)) tag_ptr
    
        -- Poke in the data
        forM (xs `zip` [1..]) $ \(x, offset) -> do
            field_ptr <- getElementPtr data_ptr (offset :: Int32, ())
            value_ptr <- compileVar env x
            store value_ptr field_ptr
    
        bitcast data_ptr
    Lambda x e -> error "TODO: unimplemented"


mapAccumLM :: (Monad m) => (acc -> x -> m (acc, y)) -> acc -> [x] -> m (acc, [y])
mapAccumLM _ s []     = return (s, [])
mapAccumLM f s (x:xs) = do
     (s', y)  <- f s x
     (s'',ys) <- mapAccumLM f s' xs
     return (s'',y:ys)

-- Impredicative types do not seem to work too well (I can't get the call site to type-check),
-- so I'm working around the issue with this small wrapper:
newtype TypeHack a m = TH { unTH :: forall r. (a -> m r) -> m r }

cpsBindN :: [TypeHack a m]
         -> ([a] -> m r)
         -> m r
cpsBindN []     k = k []
cpsBindN (r:rs) k = unTH r $ \x -> cpsBindN rs $ \xs -> k (x:xs)
