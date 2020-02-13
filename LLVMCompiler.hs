-- XXXXXDDDDD

module LLVMCompiler (allToLLVM) where

import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Char as Char
import Control.Monad (void)
import Control.Monad.Reader
import Control.Monad.State
import Data.Void

import AbsLatte
import qualified AbsLatte as Latte

pre :: String
pre = "declare void @printInt(i32) ; \n define i32 @main() { \n "
post :: String
post = "ret i32 0 \n }"

type Register = String
data Loc = LocReg Register | LocAddress Register
data LLArg = LLArg LLType Ident
data LLVMRep = LLFunc LLType Ident [LLArg] [LLBlock]
data LLType = I8 | I32 | I1 | Void | LLStar LLType
type LLVMonad a = ReaderT (Map Ident Loc, Map Ident Type) (StateT Int (Writer [LLVMRep])) a
--map ident type żeby wiedzieć czy plus to na inty czy str. wszystkie topdefy i wszystkie zmienne
--update widoczność zmiennych -> B locktoLLVM

typeToLLType :: Type -> LLType
typeToLLType Int = I32
typeToLLType Str = LLStar I8
typeToLLType Bool = I1
typeToLLType Latte.Void = Void
typeToLLType (Arr t) = LLStar $ TypeToLLType t
typeToLLType _ = error "we dont expect such advanced types"
argToLLArg :: Arg -> LLArg
argToLLArg (Arg t i) = LLArg (typeToLLType t) i

runLLVMonad :: LLVMonad a -> [LLVMRep]
runLLVMonad a = execWriter (evalStateT (runReaderT a (Map.empty, Map.empty)) 0)

generateCode :: [LLVMRep] -> String
-- TODO #4 na sam koniec, matchowanie

programToLLVM :: Program -> String
programToLLVM (Program l) = generateCode (runLLVMonad (mapM_ topDefToLLVM l) )

topDefToLLVM :: TopDef -> LLVMonad ()
topDefToLLVM (FnDef t ident args block) = do
  censor ((:[]) . LLFunc (typeToLLType t) ident (map argToLLArg args)) $ blockToLLVM block
-- TODO #3 widoczność zmiennych
blockToLLVM :: Block -> LLVMonad ()
blockToLLVM (Block (Decl t items):tail) = do
  --TODO #3 generacja deklaracji, mapa nazw, update readera
blockToLLVM (Block (h:t)) = do
  stmtToLLVM h
  blockToLLVM (Block t)

blockToLLVM (Block []) = return ()
stmtToLLVM :: Stmt -> LLVMonad ()
stmtToLLVM Empty = return ()
-- TODO #1 każdy kolejny odpakować, nei moze byc Decl bo pattern match wyżej

exprToLLVM :: Expr -> LLVMonad Loc
-- TODO #2 też poodpakować, loc to miejsce w którym wynik expr



freshRegister :: LLVMonad Register
freshRegister = do
  oldRegister <- get
  put $ oldRegister + 1
  return $ "%XD" ++ show (oldRegister + 1)