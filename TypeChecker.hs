module TypeChecker () where

import Data.Map (Map, (!))
import qualified Data.Map as Map
import qualified Data.Char as Char
import Control.Monad (void)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Data.Void

import AbsLatte
import qualified AbsLatte as Latte

type TypeMonad a = ReaderT (Map Ident Type, Type) (Except String) a

runTypeMonad :: TypeMonad a -> Either String a
runTypeMonad a = runExcept $ runReaderT a

checkTypes :: Program -> Bool

checkTypes a = runTypeMonad $ checkProgram a

checkProgram :: Program -> TypeMonad ()

checkProgram (Program list) = do
  let fnTypes = Map.fromList $ getTypes list
  local (const fnTypes) (mapM_ checkTopDef list)


getTypes ::  [TopDef] -> [(Ident, Type)]
getTypes = map getType

---uhhhh
getType :: TopDef -> (Ident, Type)

getType (FnDef t ident arg block) =  (ident, Fun t unpackTypes $ arg)

unpackTypes :: [Arg] -> [Type]
unpackTypes = map unpackType
unpackType :: Arg -> Type
unpackType Arg t i = t

makePair :: Arg -> (Ident, Type)
makePair (Arg t i) = (i, t)
checkTopDef :: TopDef -> TypeMonad ()

checkTopDef (TopDef t ident args block) = do
  let map = Map.fromList (map makePair args)
      newReader = (map, t)
  local (const newReader) $ checkBlock block

getIdent :: Item -> Ident
getIdent (NoInit i) = i
getIdent (Init i expr ) = i

first :: (a -> c) -> (a, b) -> (c, b)
first f ~(a, b) = (f a, b)

second :: (b -> c) -> (a, b) -> (a, c)
second f ~(a, b) = (a, f b)

checkBlock :: Block -> TypeMonad ()
checkBlock (Block []) = return ()
checkBlock (Block (stmt@(Decl t item):tail)) = do
  let map = Map.fromList (zip (map getIdent item) (repeat t))
  checkStmt stmt
  local (first (Map.union map) ) $ checkBlock (Block tail)

checkBlock(Block (head:tail)) = do
  checkStmt head
  checkBlock (Block tail)





getType :: Ident -> TypeMonad Type
getType i = do
  r <- asks fst
  unless (Map.member i r) $ throwError "undefined XD"
  return (r ! i)
checkStmt :: Stmt -> TypeMonad()
checkStmt Empty = return ()
checkStmt (Bstmt b) = checkBlock b
checkStmt (Decl t i) = mapM_ (checkItem t) i
checkStmt (Ass ident expr) = do
  t <- checkExpr expr
  ti <- getType ident
  unless (t == ti) $ throwError "wrong types XD"
checkStmt (Incr ident) = do
  t <- getType ident
  unless (t == Latte.Int) $ throwError "wrong type for increasing XD"

checkStmt (Decr ident) = do
  t <- getType ident
  unless (t == Latte.Int) $ throwError "wrong type for decreasing XD"

checkStmt (Ret expr) = do
  t <- checkExpr expr
  tret <- asks snd
  unless (t == tret) $ throwError "wrong type returned"

checkStmt VRet = do
  t <- asks snd
  unless (t == Latte.Void) $ throwError "wrong type returned"

checkStmt (Cond expr stmt) = do
  t <- checkExpr expr
  unless (t == Latte.Bool) $ throwError "wrong type of logica condition"
  checkStmt stmt

checkStmt (CondElse expr stmt1 stmt2) = do
  t <- checkExpr expr
  unless (t == Latte.Bool) $ throwError "wrong type of logica condition"
  checkStmt stmt
  checkStmt stmt2

checkStmt (While expr stmt) = do
  t <- checkExpr expr
  unless (t == Latte.Bool) $ throwError "wrong type of logica condition"
  checkStmt stmt

checkStmt (Cond expr stmt) = do
  t <- checkExpr expr
  unless (t == Latte.Bool) $ throwError "wrong type of logica condition"
  checkStmt stmt

checkStmt (SExp expr) =  checkExpr expr





checkItem :: Type -> Item -> TypeMonad()
checkItem t (NoInit i ) =  return ()
checkItem t (Init ident expr) =do
  t1 <- checkExpr expr
  unles (t == t1) $ throwError "wrong type XD"

isFunctional :: Type -> Bool
isFunctional (Fun _ _) = True
isFunctional _ = False

checkExpr :: Expr -> TypeMonad Type
checkExpr (Evar ident) = getType ident
checkExpr (ELitInt integer) = return Latte.Int
checkExpr ELitTrue = return Latte.Bool
checkExpr ELitFalse = return Latte.Bool
checkExpr EApp ident exprs = do
  t <- getType ident
  types <- mapM checkExpr exprs
  unless (isFunctional t) $ throwError "wrong type"
  let Fun retT argTs = t
  unless (argTs == types) $throwError "wrong type"
  return retT

checkExpr EString string = return Latte.Str
checkExpr Neg expr = do
  t <- checkExpr expr
  unless (t == Latte.Int) $ throwError "wrong type"
  return Latte.Int
checkExpr Not expr = do
  t <- checkExpr expr
  unless (t == Latte.Bool ) $ throwError "wrong type"
  return Latte.Int

checkExpr (EMul exp1 _ exp2) = do
  t1 <- checkExpr exp1
  t2 <- checkExpr exp2
  unless (t1 == Latte.Int) $ throwError "wrong type"
  unless (t2 == Latte.Int) $ throwError "wrong type"
  return Latte.Int


checkExpr (EAdd exp1 Plus exp2) = do
  t1 <- checkExpr exp1
  t2 <- checkExpr exp2
  unless (t1 == Latte.Int || t1 == Latte.Str) $ throwError "wrong type"
  unless (t2 == Latte.Int || t2 == Latte.Str) $ throwError "wrong type"
  unless (t1 == t2) $ throwError "wrong type"
  return t1

checkExpr (EAdd exp1 _ exp2) = do
  t1 <- checkExpr exp1
  t2 <- checkExpr exp2
  unless (t1 == Latte.Int) $ throwError "wrong type"
  unless (t2 == Latte.Int) $ throwError "wrong type"
  return Latte.Int

 checkExpr (ERel exp1 op exp2) = do
   t1 <- checkExpr exp1
   t2 <- checkExpr exp2
   if op `elem` [LTH, LE, GTH, GE] then do
     unless (t1 == Latte.Int) $ throwError "wrong type"
     unless (t2 == Latte.Int) $ throwError "wrong type"
     return Latte.Bool
   else do
     unless (t1 == t2) $ throwError "wrong type"
     return Latte.Bool


checkExpr (EAnd exp1 _ exp2) = do
  t1 <- checkExpr exp1
  t2 <- checkExpr exp2
  unless (t1 == Latte.Bool) $ throwError "wrong type"
  unless (t2 == Latte.Bool) $ throwError "wrong type"
  return Latte.Bool

checkExpr (EOr exp1 _ exp2) = do
  t1 <- checkExpr exp1
  t2 <- checkExpr exp2
  unless (t1 == Latte.Bool) $ throwError "wrong type"
  unless (t2 == Latte.Bool) $ throwError "wrong type"
  return Latte.Bool

