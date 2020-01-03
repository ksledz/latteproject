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

type LLVMonad a = ReaderT (Map Ident String) (State Int) a

freshRegister :: LLVMonad String
freshRegister = do
  oldRegister <- get
  put $ oldRegister + 1
  return $ "%XD" ++ show (oldRegister + 1)