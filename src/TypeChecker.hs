module TypeChecker (checkTypes) where

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

data TCType = TCInt | TCStr | TCBool | TCVoid | TCFun TCType [TCType] deriving Eq

type TypeMonad a = ReaderT (Map Ident TCType, TCType) (Except String) a

runTypeMonad :: TypeMonad a -> Either String a
runTypeMonad a = runExcept $ runReaderT a  (Map.empty, TCVoid) 

checkTypes :: Program a -> Either String ()

checkTypes a = runTypeMonad $ checkProgram a

checkProgram :: Program a -> TypeMonad ()

checkProgram (Program _ list) = do
  let fnTypes = Map.fromList $ getTopTypes list
  local (const (fnTypes, TCVoid)) (mapM_ checkTopDef list) 


getTopTypes ::  [TopDef a] -> [(Ident, TCType)]
getTopTypes = map getTopType

getTopType :: TopDef a -> (Ident, TCType)

getTopType (FnDef _ t ident arg block) =  (ident, TCFun (convertType t) (unpackTypes arg))

unpackTypes :: [Arg a] -> [TCType]
unpackTypes = map unpackType
unpackType :: Arg a -> TCType
unpackType (Arg _ t i) = convertType t

convertType :: Type a -> TCType
convertType (Latte.Int _) = TCInt
convertType (Latte.Str _) = TCStr
convertType (Latte.Bool _) = TCBool
convertType (Latte.Void _) = TCVoid

makePair :: Arg a -> (Ident, TCType)
makePair (Arg _ t i) = (i, convertType t)

checkTopDef :: TopDef a -> TypeMonad ()

checkTopDef (FnDef _ t ident args block) = do
  let newVars = Map.fromList (map makePair args)
  local (first (Map.union newVars))  $ checkBlock block

getIdent :: Item a -> Ident
getIdent (NoInit _ i) = i
getIdent (Init _ i expr ) = i

first :: (a -> c) -> (a, b) -> (c, b)
first f ~(a, b) = (f a, b)

second :: (b -> c) -> (a, b) -> (a, c)
second f ~(a, b) = (a, f b)

checkBlock :: Block a -> TypeMonad ()
checkBlock (Block _ []) = return ()
checkBlock (Block loc (stmt@(Decl _ t item):tail)) = do
  let newVars = Map.fromList (zip (map getIdent item) (repeat (convertType t)))
  checkStmt stmt
  local (first (Map.union newVars) ) ( checkBlock (Block loc tail))

checkBlock(Block loc (head:tail)) = do
  checkStmt head
  checkBlock (Block loc tail)


-- TODO loc
getType :: Ident -> TypeMonad TCType
getType i = do
  r <- asks fst
  unless (Map.member i r) $ throwError "undefined XD"
  return (r ! i)
checkStmt :: Stmt a -> TypeMonad()
checkStmt (Empty _) = return ()
checkStmt (BStmt _ b) = checkBlock b
checkStmt (Decl _ t i) = mapM_ (checkItem $ convertType t) i
checkStmt (Ass loc ident expr) = do
  t <- checkExpr expr
  ti <- getType ident
  unless (t == ti) $ throwError "wrong types XD"
checkStmt (Incr loc ident) = do
  t <- getType ident
  unless (t == TCInt) $ throwError "wrong type for increasing XD"

checkStmt (Decr loc ident) = do
  t <- getType ident
  unless (t == TCInt) $ throwError "wrong type for decreasing XD"

checkStmt (Ret loc expr) = do
  t <- checkExpr expr
  tret <- asks snd
  unless (t == tret) $ throwError "wrong type returned"

checkStmt (VRet loc) = do
  t <- asks snd
  unless (t == TCVoid) $ throwError "wrong type returned"

checkStmt (Cond loc expr stmt) = do
  t <- checkExpr expr
  unless (t == TCBool) $ throwError "wrong type of logica condition"
  checkStmt stmt

checkStmt (CondElse loc expr stmt1 stmt2) = do
  t <- checkExpr expr
  unless (t == TCBool) $ throwError "wrong type of logica condition"
  checkStmt stmt1
  checkStmt stmt2

checkStmt (While loc expr stmt) = do
  t <- checkExpr expr
  unless (t == TCBool) $ throwError "wrong type of logica condition"
  checkStmt stmt

checkStmt (SExp _ expr) = do checkExpr expr; return ()


checkItem :: TCType -> Item a -> TypeMonad()
checkItem t (NoInit _ i ) =  return ()
checkItem t (Init loc ident expr) =do
  t1 <- checkExpr expr
  unless (t == t1) $ throwError "wrong type XD"

isFunctional :: TCType -> Bool
isFunctional (TCFun _ _) = True
isFunctional _ = False

checkExpr :: Expr a -> TypeMonad TCType
checkExpr (EVar _ ident) = getType ident
checkExpr (ELitInt _ integer) = return TCInt
checkExpr (ELitTrue _) = return TCBool
checkExpr (ELitFalse _) = return TCBool
checkExpr (EApp loc ident exprs) = do
  t <- getType ident
  types <- mapM checkExpr exprs
  unless (isFunctional t) $ throwError "wrong type"
  let TCFun retT argTs = t
  unless (argTs == types) $ throwError "wrong type"
  return retT

checkExpr (EString _ string) = return TCStr
checkExpr (Neg loc expr) = do
  t <- checkExpr expr
  unless (t == TCInt) $ throwError "wrong type"
  return TCInt
checkExpr (Not loc expr) = do
  t <- checkExpr expr
  unless (t == TCBool ) $ throwError "wrong type"
  return TCBool

checkExpr (EMul loc exp1 _ exp2) = do
  t1 <- checkExpr exp1
  t2 <- checkExpr exp2
  unless (t1 == TCInt) $ throwError "wrong type"
  unless (t2 == TCInt) $ throwError "wrong type"
  return TCInt


checkExpr (EAdd loc exp1 (Plus loc2) exp2) = do
  t1 <- checkExpr exp1
  t2 <- checkExpr exp2
  unless (t1 == TCInt || t1 == TCStr) $ throwError "wrong type"
  unless (t2 == TCInt || t2 == TCStr) $ throwError "wrong type"
  unless (t1 == t2) $ throwError "wrong type"
  return t1

checkExpr (EAdd loc exp1 _ exp2) = do
  t1 <- checkExpr exp1
  t2 <- checkExpr exp2
  unless (t1 == TCInt) $ throwError "wrong type"
  unless (t2 == TCInt) $ throwError "wrong type"
  return TCInt

checkExpr (ERel loc exp1 op exp2) = do
   t1 <- checkExpr exp1
   t2 <- checkExpr exp2
   let isrel = case op of LTH _ -> True
                          LE _ -> True
                          GTH _ -> True
                          GE _ -> True 
                          _ -> False 
   if isrel then do
     unless (t1 == TCInt) $ throwError "wrong type"
     unless (t2 == TCInt) $ throwError "wrong type"
   
   else do
     unless (t1 == t2) $ throwError "wrong type"
   return TCBool

checkExpr (EAnd loc exp1 exp2) = do
  t1 <- checkExpr exp1
  t2 <- checkExpr exp2
  unless (t1 == TCBool) $ throwError "wrong type"
  unless (t2 == TCBool) $ throwError "wrong type"
  return TCBool

checkExpr (EOr loc exp1 exp2) = do
  t1 <- checkExpr exp1
  t2 <- checkExpr exp2
  unless (t1 == TCBool) $ throwError "wrong type"
  unless (t2 == TCBool) $ throwError "wrong type"
  return TCBool

