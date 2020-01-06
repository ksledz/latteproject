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

pre :: String
pre = "declare void @printInt(i32) ; \n define i32 @main() { \n "
post :: String
post = "ret i32 0 \n }"

type Register = String
data Loc = LocReg Register | LocAddress Register
data LLVMRep = XD
type LLVMonad a = ReaderT (Map Ident Loc, Map Ident Type) (StateT Int (Writer [LLVMRep])) a
--map ident type żeby wiedzieć czy plus to na inty czy str. wszystkie topdefy i wszystkie zmienne
--update widoczność zmiennych -> B locktoLLVM

runLLVMonad :: LLVMonad a -> [LLVMRep]
-- runreader evalstate execwriter

generateCode :: [LLVMRep] -> String

programToLLVM :: Program -> String

topDefToLLVM :: TopDef -> LLVMonad ()

blockToLLVM :: Block -> LLVMonad ()

stmtToLLVM :: Stmt -> LLVMonad ()

exprToLLVM :: Expr -> LLVMonad Loc



freshRegister :: LLVMonad Register
freshRegister = do
  oldRegister <- get
  put $ oldRegister + 1
  return $ "%XD" ++ show (oldRegister + 1)