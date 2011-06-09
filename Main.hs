{-# LANGUAGE Rank2Types, ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wall -fno-warn-name-shadowing #-}
module Main (main) where

import Control.Arrow (second)
import Control.Monad
import Control.Monad.IO.Class

import Data.Int
import Data.Word
import Data.List
import Data.IORef

import qualified Data.Map as M
import qualified Data.Set as S

import System.IO (fixIO)

import Foreign.Ptr

import LLVM.Core
import LLVM.ExecutionEngine


-- The language to supercompile
-- ============================
--
-- We compile a standard pure, strict, higher-order functional language
-- with algebraic data, case statements, literals and primitive operations.
--
-- The language has two additional constructors Weaken and Delay that can
-- be used by the producer of the term to mark certainly-unused variables
-- and where compilation should be delayed.

type Var = String

type Literal = Int32

data DataCon = DC { dataConName :: String, dataConTag :: Int32 }

data PrimOp = Add | Subtract | Multiply

data Term = Var Var
          | Value Val
          | App Term Var
          | Case Term [(DataCon, [Var], Term)]
          | LetRec [(Var, Val)] Term
          | Let Var Term Term
          | PrimOp PrimOp [Term]
          | Weaken Var Term -- Used to "forget" certain variables so we can keep closure size down even in the presence of Delay
          | Delay Term      -- The compiler is non-strict in the contained Term. Generates code that returns control to the compiler

data Val = Lambda Var Term
         | Data DataCon [Var]
         | Literal Literal


-- Compilation
-- ===========

-- | We use this type to represent values in our system that are *either*
-- pointers to heap allocated closures/data *or* immediate Int32 values.
--
-- LLVM forbids void pointers, so we use the reccomended replacement:
type VoidPtr = Ptr Int8

-- | All we need to know about the environment in which we compile our code is
-- what the Values of the in-scope variables are. Note that LLVM Values actually
-- correspond to SSA variable names, so this is really which LLVM variable holds
-- the data at the moment
data CompileEnv = CE {
    symbolValues :: M.Map Var (Value VoidPtr)
  }

-- | Sometimes we will need to generate a global variable in some module which we
-- refer to later in a different module. However, we wish to create the closure
-- that (when entered) defines the later module *before* we know the address
-- of that global variable.
--
-- We work around this ordering problem by using a "linker". When generating the first
-- module we will find the address that the JITted global variable lives at. This
-- address will be stored in an IORef after we find out what it is. The address can then
-- be retrieved by the later module (when it actually needs it) by reading the IORef.
type LinkableType = Ptr (Ptr VoidPtr -> IO VoidPtr) -- Keep the system monotyped for now, for simplicity
data CompileState = CS {
    linkDemands :: [(Global LinkableType, Ptr LinkableType -> IO ())]
      -- ^ The globals we want the address of, and a function that we should call to store each address
  }


-- | Top level compilation: just invokes compilation for an expression, with additional marshalling from
-- the result type into Int32 (for simplicity, we assume all programs evaluate to Int32).
compileTop :: Term -> CodeGenModule (CompileState, Function (IO Int32))
compileTop e = tunnelIO (createFunction InternalLinkage) $
                 compile (CE { symbolValues = M.empty }) (CS { linkDemands = [] }) e $
                   \s value_ptr -> fmap (const s) $ do
                       x <- ptrtoint value_ptr :: CodeGenFunction Int32 (Value Int32)
                       ret x :: CodeGenFunction Int32 Terminate

-- | Compilation of a term. This generates LLVM opcodes and basic blocks within the context of a LLVM
-- Function, so that a particular Value holds the value of the expression being compiled.
compile :: forall r a.
           CompileEnv   -- ^ The Values for each member of our lexical environment
        -> CompileState -- ^ Any pending link information
        -> Term         -- ^ Term to compile
        -> (CompileState -> Value VoidPtr -> CodeGenFunction r a)
           -- ^ Continuation: we call this in order to continue compiling the consumer of this value
        -> CodeGenFunction r a
compile env s (Var x) k = compileVar env x >>= k s
compile env s (Value v) k = case compileValue (M.keysSet (symbolValues env)) v of
    Immediate get_value_ptr -> get_value_ptr >>= k s
    HeapAllocated nwords poke -> do
        -- We don't bother with garbage collection: just malloc some memory whenever we need it
        value_ptr <- arrayMalloc nwords
        s <- poke env s value_ptr
        bitcast value_ptr >>= k s
compile env s (App e x) k = compile env s e $ \s closure_ptr -> do
    arg_ptr <- compileVar env x
    
    -- Retrieve the function pointer from the first field of the closure:
    fun_ptr_ptr <- bitcast closure_ptr :: CodeGenFunction r (Value (Ptr (Ptr (VoidPtr -> VoidPtr -> IO VoidPtr))))
    fun_ptr <- load fun_ptr_ptr
    
    -- We need to supply the closure itself in the call to the function pointer, so that the
    -- function can access its own lexical environment:
    call fun_ptr closure_ptr arg_ptr >>= k s
compile env s (Case e alts) k = compile env s e $ \s data_ptr -> do
    -- Retrieve the tag from the first field of the data constructor:
    tag_ptr <- bitcast data_ptr :: CodeGenFunction r (Value (Ptr Int32))
    tag <- load tag_ptr
    
    -- Prepare the names of tail blocks, and the code that generates them.
    -- We need a tail block for each branch, one for the (hopefully impossible)
    -- case where the tag we got didn't match anything, and one block that all the
    -- branches of the case will jump to to join up control flow again. The basic
    -- blocks look like this (control enters at the top):
    --
    --         entry
    --       /   |   \
    --      v    v    v
    --   Tag 0  Tag 1  No match!
    --     \     |
    --      v    v
    --     join point
    join_block <- newBasicBlock
    panic_block <- newBasicBlock
    (blocks, define_blocks) <- fmap unzip $ forM alts $ \(dc, xs, e) -> do
        alt_block <- newBasicBlock
        let -- We're not defining the block *just* yet, since we haven't even emitted the switch:
            define_block s = do
              defineBasicBlock alt_block
              -- When defining a block corresponding to a case branch, we first need to load
              -- the fields of the data constructor so we can add them to the lexical env
              field_base_ptr <- bitcast data_ptr :: CodeGenFunction r (Value (Ptr VoidPtr))
              env <- forAccumLM_ env (xs `zip` [1..]) $ \env (x, offset) -> do
                  field_ptr <- getElementPtr field_base_ptr (offset :: Int32, ())
                  value_ptr <- load field_ptr
                  return (env { symbolValues = M.insert x value_ptr (symbolValues env) })
              -- Compile the code from the branch itself: when the branch returns, jump to the join block
              (s, result_ptr) <- compile env s e $ \s result_ptr -> br join_block >> return (s, result_ptr)
              return (s, (result_ptr, alt_block))
        return ((constOf (dataConTag dc), alt_block), define_block)
    
    -- Jump into appropriate branch according to the tag we just found:
    switch tag panic_block blocks
    
    -- We've now completed the main block (it ends with that switch). Now define the tail code:
    (s, phi_data) <- accumLM s define_blocks -- Blocks for each branch first
    defineBasicBlock panic_block -- If no tag matches, do something undefined
    unreachable
    defineBasicBlock join_block -- When any branch completes, come back here.
    phi phi_data >>= k s        -- We need a phi node to join the results from each branch.
compile env s (Let x e_bound e_body) k = compile env s e_bound $ \s bound_ptr -> do
    compile (env { symbolValues = M.insert x bound_ptr (symbolValues env) }) s e_body k
compile env s (LetRec xvs e_body) k = do
    -- Decide how each value will be allocated (immediate or heap allocated)
    let avails = S.fromList (map fst xvs) `S.union` M.keysSet (symbolValues env)
        (nwords, get_value_ptrs_pokes) = forAccumL 0 xvs $ \nwords_total (x, v) -> case compileValue avails v of
                                                                     Immediate get_value_ptr   -> (nwords_total,          (x, \_         -> get_value_ptr >>= bitcast,                  Nothing))
                                                                     HeapAllocated nwords poke -> (nwords_total + nwords, (x, \block_ptr -> getElementPtr block_ptr (nwords_total, ()), Just poke))
    
    -- Allocate enough memory for all the values to fit in
    block_ptr <- arrayMalloc nwords
    -- Now we have the block pointer and the size of each value, we can predict the values each
    -- variable actually has before we actually intialize the heap memory they point to (if appropriate).
    -- This is essential to tie the knot, because in order to do that initialisation I need to know
    -- what the updated lexical environment is.
    (value_ptrs, pokes) <- fmap unzip $ forM get_value_ptrs_pokes $ \(x, get_value_ptr, mb_poke) -> do
        value_ptr <- get_value_ptr block_ptr
        value_ptr' <- bitcast value_ptr :: CodeGenFunction r (Value VoidPtr)
        return ((x, value_ptr'), \env s -> maybe (return s) (\poke -> poke env s value_ptr) mb_poke :: CodeGenFunction r CompileState)
    
    -- Create the extended environment with the new predictions, and actually initialize the values by using that environment
    let env' = env { symbolValues = M.fromList value_ptrs `M.union` symbolValues env }
    s <- forAccumLM_ s pokes (\s poke -> poke env' s)
    
    compile env' s e_body k
compile env s (PrimOp pop es) k
  = cpsBindN [TH (\s (k :: CompileState -> Value Int32 -> m b) -> compile env s e $ \s value_ptr -> ptrtoint value_ptr >>= k s)
             | e <- es] s $ \s arg_ints -> do
    res_int <- case (pop, arg_ints) of
        (Add,      [i1, i2]) -> add i1 i2
        (Subtract, [i1, i2]) -> sub i1 i2
        (Multiply, [i1, i2]) -> mul i1 i2
        _ -> error "Bad primitive operation arity"
    inttoptr res_int >>= k s
compile env s (Weaken x e) k = compile (env { symbolValues = M.delete x (symbolValues env) }) s e k
compile env s (Delay e) k = do
    -- Create a block of memory we can use to marshal our lexical environment around.
    -- We poke our entire lexical environment into this array in an arbitrary order.
    -- Every member of the lexical environmont may potentially be required by the code in the Delay.
    block_ptr <- arrayAlloca (fromIntegral (M.size (symbolValues env)) :: Word32)
    get_block_value_ptrs <- forM ([0..] `zip` M.toList (symbolValues env)) $ \(offset, (x, value_ptr)) -> do
        field_ptr <- getElementPtr (block_ptr :: Value (Ptr VoidPtr)) (offset :: Int32, ())
        store value_ptr field_ptr
        return $ \block_ptr -> do
            field_ptr <- getElementPtr block_ptr (offset, ())
            fmap ((,) x) $ load field_ptr
    
    -- The code for a Delay transfers control to the function pointer stored in this global. The idea is that:
    --  1) The first time round, this is a pointer to a function that jumps back into Haskell and then reinvokes
    --     LLVM to compile the rest of the term. After compilation of the rest of the term (in a new Module),
    --     Haskell then rewrites this function pointer to point to the new code, and jumps into that newly-compiled
    --     code.
    --  2) On subsequent entries to the Delayed code, we call the function pointer and just jump into the code
    --     that was previously compiled by the Haskell trampoline. So we enter Haskell code at most once per Delay,
    --     which saves cycles (and is more elegant).
    --
    -- I tried to use named globals to link the later module to the earlier one, but LLVM's JIT didn't seem to
    -- like it: it couldn't link the name in the later module to the previously-defined one. I have no idea why.
    -- The workaround is the linker stuff with IORefs in the CompilerState.
    trampoline_global_ptr_ref <- liftIO $ newIORef $ error "compile(Delay): IORef not filled"
    
    -- Create the Haskell trampoline that will be invoked when we first need to compile this:
    reenter_compiler_ptr <- liftIO $ fixIO $ \reenter_compiler_ptr -> wrapDelay $ \block_ptr -> do
        -- Build a Module containing:
        --  1. The replacement code, corresponding to compiling the contents of the Delay
        --  2. Fixup code that rewrites the global and then transfers control to the replacement code
        fixup_func <- compileAndLink $ do
            -- At the point we get in here, the previous round of linking has totally finished, but compiling
            -- the body might generate new link demands. Start again with empty linkDemands.
            s <- return $ CS { linkDemands = [] }
            (s, replacement_func_value) <- tunnelIO1 (createFunction InternalLinkage) $ \(block_ptr :: Value (Ptr VoidPtr)) -> do
                -- Create a new lexical environment by pulling values out of the block of memory
                -- containing the lexical environment of the caller, then compile the delayed code.
                value_ptrs <- mapM ($ block_ptr) get_block_value_ptrs
                compile (CE { symbolValues = M.fromList value_ptrs }) s e (\s value_ptr -> fmap (const s) (ret value_ptr))
            
            -- This is the fixup function:
            trampoline_global_ptr <- liftIO $ readIORef trampoline_global_ptr_ref
            fmap ((,) s . generateFunction) $ createFunction InternalLinkage $ \block_ptr -> do
                -- Make sure that next time we execute this Delay we jump right to the replacement
                trampoline_global <- staticGlobal False trampoline_global_ptr :: CodeGenFunction VoidPtr (Global (Ptr (Ptr VoidPtr -> IO VoidPtr)))
                store replacement_func_value trampoline_global
                -- Call the replacement code right now to get the work done
                call replacement_func_value block_ptr >>= ret
        
        -- Now that we've compiled the new module, invoke the fixup function:
        freeHaskellFunPtr reenter_compiler_ptr -- TODO: I probably shouldn't free this function while it is still running!
        fixup_func block_ptr
    
    -- Create the global variable that will hold the trampoline function pointer
    trampoline_global <- liftCodeGenModule $ createGlobal False ExternalLinkage (constOf (castFunPtrToPtr reenter_compiler_ptr))
    s <- return $ s { linkDemands = (trampoline_global, writeIORef trampoline_global_ptr_ref) : linkDemands s }
    
    -- Generate code that transfers control to the trampoline
    trampoline_ptr <- load trampoline_global
    call trampoline_ptr block_ptr >>= k s

foreign import ccall "wrapper"
    wrapDelay :: (Ptr VoidPtr -> IO VoidPtr) -> IO (FunPtr (Ptr VoidPtr -> IO VoidPtr))

-- | We already have a LLVM Value corresponding to each variable in the lexical environment, so this is easy.
compileVar :: CompileEnv -> Var -> CodeGenFunction r (Value VoidPtr)
compileVar env x = case M.lookup x (symbolValues env) of
    Nothing        -> error $ "Unbound variable " ++ show x
    Just value_ptr -> return value_ptr

-- | We say that values of the language ar heap allocated if the corresponding (Value VoidPtr) points to the block of heap
-- memory in which they reside. By constrast, if values are immediate the corresponding (Value VoidPtr) isn't a pointer at all,
-- but is rather just a cast version of the actual data.
--
-- Currently, only Int32s are immediate: functions and data constructors are HeapAllocated.
data ValueBuilder = Immediate (forall r. CodeGenFunction r (Value VoidPtr))
                  | HeapAllocated Word32 (forall r. CompileEnv -> CompileState -> Value (Ptr VoidPtr) -> CodeGenFunction r CompileState)
                       -- ^ Contains the number of words we need to allocate to fit the value, and a function to invoke to fill that memory

compileValue :: S.Set Var -> Val -> ValueBuilder
compileValue avails v = case v of
    -- Do not allocate space: we will pack Int32s into pointers
    -- NB: this code assumes Int32s fit into pointers! Probably safe, but...
    Literal l  -> Immediate $ inttoptr (valueOf l)
    -- Allocate space for one pointer per data item, and one pointer for the tag.
    --
    -- For example, the list [10] looks like this in memory:
    --
    --                /-------\     /-------\
    --   value_ptr--->|   1   |  /->|   0   |
    --                +-------+  |  \-------/
    --                |   10  |  |
    --                +-------+  |
    --                |   .   |--/
    --                \-------/
    --
    -- (Cons has the tag 1, and Nil uses the tag 0). Addresses increase down the screen,
    -- so the leftmost field occupies a lower memory address than the rightmost one.
    Data dc xs -> HeapAllocated (1 + genericLength xs) $ \env s data_ptr -> do
        -- Poke the tag into the memory allocated for the data constructor
        tag_ptr <- bitcast data_ptr :: CodeGenFunction r (Value (Ptr Int32))
        store (valueOf (dataConTag dc)) tag_ptr
    
        -- Poke the data fields into the allocated memory. Offsets start from 1 because
        -- we reserve offset 0 for the tag itself.
        forM_ (xs `zip` [1..]) $ \(x, offset) -> do
            field_ptr <- getElementPtr data_ptr (offset :: Int32, ())
            value_ptr <- compileVar env x
            store value_ptr field_ptr
    
        return s
    -- Allocate space for one pointer per closure variable, and one pointer for the code
    --
    -- For example, the closure (let y = 10 in \x -> x + y) looks like this in memory:
    --
    --                /-------\
    --   value_ptr--->|   .   |--->code
    --                +-------+
    --                |   10  |
    --                \-------/
    --
    -- Addresses increase down the screen, so the code pointer occupies a lower memory
    -- address than any of the closed-over variables.
    Lambda x e -> HeapAllocated (1 + fromIntegral (S.size avails_used)) $ \env s closure_ptr -> do
        -- Figure out at which offset we will store each member of the lexical environment
        -- (offsets start at 1 because we reserve offset 0 for the code pointer itself).
        -- At the same time we work out what code we need to generate to pull the value out of the closure.
        let (closed_value_ptrs, get_closure_value_ptrs)
               = unzip $ flip map ([1..] `zip` M.toList (symbolValues env `restrict` avails_used)) $
                            \(offset, (x, value_ptr)) -> let get_value_ptr closure_ptr = do
                                                                field_ptr <- getElementPtr closure_ptr (offset :: Int32, ())
                                                                load field_ptr
                                                         in ((offset, value_ptr), (x, get_value_ptr))
        
        -- Define the function corresponding to the lambda body. Each lambda corresponds to a C function with two arguments:
        -- a pointer to the closure (which will contain pointers to the lexical environment), and a pointer to the argument
        (s, fun_ptr) <- liftCodeGenModule $ tunnelIO2 (createFunction InternalLinkage) $ \closure_ptr arg_ptr -> do
            -- Generate the code necessary to pull each member of the lexical environment back out
            closure_value_ptrs <- forM get_closure_value_ptrs $ \(x, get_value_ptr) -> fmap ((,) x) $ get_value_ptr closure_ptr
            -- Compile the body of the lambda, returning the value that it returns to the caller
            compile (env { symbolValues = M.insert x arg_ptr (M.fromList closure_value_ptrs) }) s e $ \s value_ptr -> fmap (const s) (ret value_ptr)
        
        -- Poke the code into the memory allocated for the closure
        fun_ptr_ptr <- bitcast closure_ptr :: CodeGenFunction r (Function (Ptr (Ptr VoidPtr -> VoidPtr -> IO VoidPtr)))
        store fun_ptr fun_ptr_ptr
        
        -- Poke the lexical environment into the closure memory
        forM_ closed_value_ptrs $ \(offset, value_ptr) -> do
            field_ptr <- getElementPtr closure_ptr (offset, ())
            store value_ptr field_ptr
        
        return s
      where avails_used = S.delete x (termFreeVars avails e) -- We only close over free variables of the lambda body


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
        -- The interesting case: we have to assume that Delay uses the whole lexical environment.
        -- This is why Weaken is important: Weaken trims this set and hence makes it less conservative.
    
    value v = case v of
      Lambda x e -> S.delete x (term e)
      Data _ xs  -> S.fromList xs
      Literal _  -> S.empty


-- Just-in-time compilation/linking
-- ================================

compileAndLink :: CodeGenModule (CompileState, EngineAccess b) -> IO b
compileAndLink bld = do
    m <- newModule
    (act, link, mappings) <- defineModule m $ do
        (s, act) <- bld
        let (linkable_funs, store_linkable_ptr_refs) = unzip (linkDemands s)
            get_linkable_fun_ptrs = mapM (fmap castFunPtrToPtr . getPointerToFunction) linkable_funs
            link = sequence_ . zipWith ($) store_linkable_ptr_refs
        fmap ((,,) (liftM2 (,) get_linkable_fun_ptrs act) link) getGlobalMappings

    --writeBitcodeToFile "/tmp/debug.bc" m

    -- At this point we have a LLVM Module but no actual assembly for it. Generate some.
    prov <- createModuleProviderForExistingModule m
    (linked_fun_ptrs, res) <- runEngineAccess $ do
        addModuleProvider prov
        addGlobalMappings mappings
        act

    -- At this stage, we have the function pointers we needed to link. Put them into the linker IORefs.
    link linked_fun_ptrs
    return res


-- Test terms and top-level driver
-- ===============================

trueDataCon, falseDataCon :: DataCon
falseDataCon = DC "False" 0
trueDataCon = DC "True" 1

nothingDataCon, justDataCon :: DataCon
nothingDataCon = DC "Nothing" 0
justDataCon = DC "Just" 1

nilDataCon, consDataCon :: DataCon
nilDataCon = DC "Nil" 0
consDataCon = DC "Cons" 1

test_term :: Term
-- Simple arithmetic:
--test_term = PrimOp Add [Value (Literal 1), Value (Literal 2)]
-- Test that exposed "let" miscompilation:
--test_term = Let "x" (Value (Literal 1)) (Value (Literal 2))
-- Simple case branches:
--test_term = Case (Value (Data trueDataCon [])) [(trueDataCon, [], Value (Literal 1)),
--                                                (falseDataCon, [], Value (Literal 2))]
-- Complex case branches:
--test_term = Let "x" (Value (Literal 5)) $
--            Case (Value (Data justDataCon ["x"]))
--              [(nothingDataCon, [], Value (Literal 1)),
--               (justDataCon, ["y"], Var "y")]
-- Simple function use. Does not need to reference closure:
--test_term = Let "x" (PrimOp Add [Value (Literal 1), Value (Literal 2)]) $
--            Value (Lambda "y" (PrimOp Multiply [Var "y", Value (Literal 4)])) `App` "x"
-- Complex function use. Needs to reference closure:
--test_term = Let "x" (PrimOp Add [Value (Literal 1), Value (Literal 2)]) $
--            Let "four" (Value (Literal 4)) $
--            Value (Lambda "y" (PrimOp Multiply [Var "y", Var "four"])) `App` "x"
-- Letrec:
--test_term = LetRec [("ones", Data consDataCon ["one", "ones"]),
--                    ("one", Literal 1),
--                    ("zero", Literal 0),
--                    ("length", Lambda "xs" (Case (Var "xs") [(nilDataCon, [], Var "zero"),
--                                                             (consDataCon, ["_", "ys"], PrimOp Add [Value (Literal 1), Var "length" `App` "ys"])])),
--                    ("list0", Data nilDataCon []),
--                    ("list1", Data consDataCon ["one", "list0"]),
--                    ("list2", Data consDataCon ["zero", "list1"])] $
--            Case (Var "ones") [(consDataCon, ["y", "ys"], PrimOp Add [Var "y", Var "length" `App` "list2"])]
-- Trivial delay
--test_term = Delay (Value (Literal 1))
-- Reentrant delay
--test_term = Let "foo" (Value (Lambda "x" (Delay (PrimOp Add [Var "x", Var "x"])))) $
--            Let "one" (Value (Literal 1)) $
--            Let "two" (Value (Literal 2)) $
--            PrimOp Add [Var "foo" `App` "one", Var "foo" `App` "two"]
-- Nested delay
test_term = Delay (Delay (Value (Literal 1)))

main :: IO ()
main = do
    initializeNativeTarget
    
    -- Compile and link
    fun <- compileAndLink $ fmap (second generateFunction) $ compileTop test_term
    
    -- Run the compiled code
    putStrLn "Here we go:"
    fun >>= print


-- Utility functions
-- =================

restrict :: Ord k => M.Map k v -> S.Set k -> M.Map k v
restrict m s = M.filterWithKey (\x _ -> x `S.member` s) m

-- Impredicative types do not seem to work too well (I can't get the call site to type-check),
-- so I'm working around the issue with this small wrapper:
newtype TypeHack s a m = TH { unTH :: forall r. s -> (s -> a -> m r) -> m r }

cpsBindN :: [TypeHack s a m]
         -> s
         -> (s -> [a] -> m r)
         -> m r
cpsBindN []     s k = k s []
cpsBindN (r:rs) s k = unTH r s $ \s x -> cpsBindN rs s $ \s xs -> k s (x:xs)

tunnelIOCore :: (MonadIO m, MonadIO n)
             => ((c -> m ()) -> n b)
             -> n (c, b)
tunnelIOCore control = do
    -- Urgh, have to resort to tunneling through IORef to get the new State out
    s_ref <- liftIO $ newIORef (error "tunnelIO: unfilled IORef")
    fun <- control $ liftIO . writeIORef s_ref
    s <- liftIO $ readIORef s_ref
    return (s, fun)

tunnelIO :: (MonadIO m, MonadIO n)
         => (m () -> n b)
         -> m c
         -> n (c, b)
tunnelIO control arg = tunnelIOCore (\c2m -> control $ arg >>= c2m)

tunnelIO1 :: (MonadIO m, MonadIO n)
          => ((arg1 -> m ()) -> n b)
          -> (arg1 -> m c)
          -> n (c, b)
tunnelIO1 control arg = tunnelIOCore (\c2m -> control $ \arg1 -> arg arg1 >>= c2m)

tunnelIO2 :: (MonadIO m, MonadIO n)
          => ((arg1 -> arg2 -> m ()) -> n b)
          -> (arg1 -> arg2 -> m c)
          -> n (c, b)
tunnelIO2 control arg = tunnelIOCore (\c2m -> control $ \arg1 arg2 -> arg arg1 arg2 >>= c2m)

accumLM :: (Monad m) => acc -> [acc -> m (acc, y)] -> m (acc, [y])
accumLM s []     = return (s, [])
accumLM s (f:fs) = do
    (s', y)  <- f s
    (s'',ys) <- accumLM s' fs
    return (s'',y:ys)

forAccumLM_ :: Monad m => acc -> [a] -> (acc -> a -> m acc) -> m acc
forAccumLM_ acc []     _ = return acc
forAccumLM_ acc (x:xs) f = do
    acc <- f acc x
    forAccumLM_ acc xs f

forAccumL :: acc -> [a] -> (acc -> a -> (acc, b)) -> (acc, [b])
forAccumL acc []     _ = (acc, [])
forAccumL acc (x:xs) f = case f acc x of (acc, y) -> case forAccumL acc xs f of (acc, ys) -> (acc, y:ys)
