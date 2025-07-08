module LeaST.CodeGen where

import LeaST.LeaST
import qualified Syntax.Base as B
import qualified Syntax.Type as T
import qualified Syntax.Kind as K

import LLVM.AST
import LLVM.AST.Global
import qualified LLVM.AST.Type as LLVM
import qualified LLVM.AST.Constant as C
import LLVM.IRBuilder
import LLVM.Context
import LLVM.Module

import Control.Monad.State
import Data.String (fromString)
import qualified Data.Map as Map

type SymbolTable = Map.Map B.Variable Operand

data CodegenEnv = CodegenEnv
  { symtab :: SymbolTable }

type Codegen = IRBuilderT (ModuleBuilderT (State CodegenEnv))

-- | Geração de código LLVM a partir de uma expressão LeaST
codegenExp :: Exp -> Codegen Operand    --TODO trocar para usar um case e ficar mais giro
codegenExp (Lit (LInt n)) = pure $ ConstantOperand $ C.Int 32 (fromIntegral n)
codegenExp (Var x) = do
  env <- lift get
  case Map.lookup x (symtab env) of
    Just op -> pure op
    Nothing -> error $ "Variável não encontrada: " ++ show x
codegenExp (Abs x _t body) = do
  let fname = fromString (B.name x)
  function fname [(LLVM.i32, ParameterName "arg")] LLVM.i32 $ \[arg] -> do
    modifySymtab (Map.insert x arg)
    codegenExp body
codegenExp (App f arg) = do
  fval <- codegenExp f
  argval <- codegenExp arg
  call fval [(argval, [])]
codegenExp _ = error "Construção ainda não suportada na geração de código LLVM."

-- | Inicializa o código e gera um módulo
generateModule :: Exp -> IO ()
generateModule expr = do
  let modAST = buildModule "leaST_module" $ do
        function "main" [] LLVM.i32 $ \_ -> do
          res <- lift $ evalStateT (runModuleBuilderT emptyModuleBuilder (runIRBuilderT emptyIRBuilder (codegenExp expr))) (CodegenEnv Map.empty)
          ret res
  withContext $ \ctx ->
    withModuleFromAST ctx modAST $ \m ->
      writeLLVMAssemblyToFile (File "output.ll") m

-- | Atualiza o symbol table
modifySymtab :: (SymbolTable -> SymbolTable) -> Codegen ()
modifySymtab f = lift $ lift $ modify (\env -> env { symtab = f (symtab env) })
