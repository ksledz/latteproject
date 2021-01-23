module TypeChecker (checkTypes) where

import Data.Map (Map, (!))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Control.Monad.Reader
import Control.Monad.Except

import AbsLatte
import qualified AbsLatte as Latte

data TCType = TCInt | TCStr | TCBool | TCVoid | TCFun TCType [TCType] | TCArray TCType | TCObject String deriving Eq
type Location = Maybe (Int, Int)
type TypeMonad a = ReaderT (Map Ident TCType, TCType) (Except (Location, String)) a

runTypeMonad :: TypeMonad a -> Either String a
runTypeMonad a = case runExcept $ runReaderT a  (Map.empty, TCVoid) of Right x -> Right x
                                                                       Left ((Just (l, c)), s) -> Left ("type error at line " ++ show l ++ ", column " ++ show c ++ ": "++ s)
                                                                       Left (Nothing, s) -> Left s
checkTypes :: Program Location -> Either String ()

checkTypes a = runTypeMonad $ checkProgram a

builtinTypes :: [(Ident, TCType)]
builtinTypes = [
        (Ident "printString", TCFun TCVoid [TCStr]),
        (Ident "printInt", TCFun TCVoid [TCInt]),
        (Ident "error", TCFun TCVoid []),
        (Ident "readInt", TCFun TCInt []),
        (Ident "readString", TCFun TCStr [])] 

checkProgram :: Program Location -> TypeMonad ()

checkProgram (Program _ list) = do
  let fnTypes = Map.fromList $ (getTopTypes list ++ builtinTypes)
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
convertType (Latte.Arr _ t) = TCArray $ convertType t
convertType (Latte.Struct _ i) = let Ident s = i in TCObject s

makePair :: Arg a -> (Ident, TCType)
makePair (Arg _ t i) = (i, convertType t)

checkTopDef :: TopDef Location -> TypeMonad ()

checkTopDef (FnDef loc t ident args block) = do
  let newVars = Map.fromList (map makePair args)
  unless ((Map.size newVars) == length(args)) $ throwError (loc, "repeating identifiers")
  res <- local ((first (Map.union newVars)).(second $ const $ convertType t)) $ checkBlock block Set.empty
  case t of
    Latte.Void _ -> return ()
    _ -> unless res $ throwError (loc, "missing return")

getIdent :: Item a -> Ident
getIdent (NoInit _ i) = i
getIdent (Init _ i expr ) = i

first :: (a -> c) -> (a, b) -> (c, b)
first f ~(a, b) = (f a, b)

second :: (b -> c) -> (a, b) -> (a, c)
second f ~(a, b) = (a, f b)

checkBlock :: Block Location -> Set Ident -> TypeMonad Bool
checkBlock (Block _ []) _ = return False
checkBlock (Block loc (stmt@(Decl _ t item):tail)) lVars = do
  let newVars = Map.fromList (zip (map getIdent item) (repeat (convertType t)))
  unless ((Map.size newVars) == length(item)) $ throwError (loc, "repeating identifiers")
  checkStmt stmt
  when (any (\i -> Set.member(getIdent i) lVars) item ) $ throwError (loc, "redefined variable")
  let newLVars = Set.union lVars (Set.fromList (map getIdent item))
  local (first (Map.union newVars) ) ( checkBlock (Block loc tail) newLVars)

checkBlock(Block loc (head:tail)) lVars = do
  res1 <- checkStmt head
  res2 <- checkBlock (Block loc tail) lVars
  return (res1 || res2)


getType :: Ident -> Location -> TypeMonad TCType
getType i loc = do
  r <- asks fst
  let Ident s = i
  unless (Map.member i r) $ throwError (loc, "undefined identifier: " ++ s)
  return (r ! i)

checkStmt :: Stmt Location -> TypeMonad Bool
checkStmt (Empty _) = return False
checkStmt (BStmt _ b) = checkBlock b Set.empty
checkStmt (Decl _ t i) = do mapM_ (checkItem $ convertType t) i; return False
checkStmt (Ass loc lval expr) = do
  t <- checkExpr expr
  ti <- checkLValue lval loc
  unless (t == ti) $ throwError (loc, "wrong types")
  return False

checkStmt (Incr loc lval) = do
  t <- checkLValue lval loc
  unless (t == TCInt) $ throwError (loc, "wrong type for increasing")
  return False

checkStmt (Decr loc lval) = do
  t <- checkLValue lval loc
  unless (t == TCInt) $ throwError (loc, "wrong type for decreasing")
  return False

checkStmt (Ret loc expr) = do
  t <- checkExpr expr
  tret <- asks snd
  unless (t == tret) $ throwError (loc, "wrong type returned")
  return True

checkStmt (VRet loc) = do
  t <- asks snd
  unless (t == TCVoid) $ throwError (loc, "wrong type returned")
  return True

checkStmt (Cond loc expr stmt) = do
  t <- checkExpr expr
  unless (t == TCBool) $ throwError (loc, "wrong type of logic condition")
  res <- checkStmt stmt
  case expr of 
    ELitTrue _ -> return res
    _ -> return False

checkStmt (CondElse loc expr stmt1 stmt2) = do
  t <- checkExpr expr
  unless (t == TCBool) $ throwError (loc, "wrong type of logic condition")
  res1 <- checkStmt stmt1
  res2 <- checkStmt stmt2
  case expr of
    ELitTrue _ -> return res1
    ELitFalse _ -> return res2
    _ -> return (res1 && res2)

checkStmt (While loc expr stmt) = do
  t <- checkExpr expr
  unless (t == TCBool) $ throwError (loc, "wrong type of logic condition")
  res <- checkStmt stmt
  case expr of
    ELitTrue _ -> return True
    _ -> return False

checkStmt (For loc t ident expr stmt) = do
  let t1 = convertType t
  t2 <- checkExpr expr
  unless (t2 == TCArray t1) $ throwError (loc, "wrong type of loop variable")
  local (first (Map.insert ident t1) ) $ checkStmt stmt



checkStmt (SExp _ expr) = do checkExpr expr; return False


checkLValue:: Expr Location -> Location -> TypeMonad TCType
checkLValue expr loc= do
  case expr of
    EVar _ _ -> return()
    EField _ _ _ -> return ()
    EIndex _ _ _ -> return ()
    _ -> throwError (loc, "invalid l-value")
  checkExpr expr



checkItem :: TCType -> Item Location -> TypeMonad()
checkItem t (NoInit _ i ) =  return ()
checkItem t (Init loc ident expr) = do
  t1 <- checkExpr expr
  unless (t == t1) $ throwError (loc, "wrong type of initializer")

isFunctional :: TCType -> Bool
isFunctional (TCFun _ _) = True
isFunctional _ = False

checkExpr :: Expr Location -> TypeMonad TCType
checkExpr (EVar loc ident) = getType ident loc
checkExpr (ELitInt _ integer) = return TCInt
checkExpr (ELitTrue _) = return TCBool
checkExpr (ELitFalse _) = return TCBool
checkExpr (EArr loc t expr) = do
  t1 <- checkExpr expr
  unless (t1 == TCInt) $ throwError (loc, "wrong array length type")
  return $ TCArray $ convertType t

checkExpr (EIndex loc e1 e2) = do
  t1 <- checkExpr e1
  t2 <- checkExpr e2
  unless (t2 == TCInt) $ throwError (loc, "wrong array index type")
  case t1 of
    TCArray t -> return t
    _ -> throwError (loc, "sweet jesus, pooh! that's not an array-able type")

checkExpr (EField  loc expr ident) = do
  t1 <- checkExpr expr
  let Ident s = ident
  case t1 of
    TCArray _ -> do
      if (s == "length") then return TCInt else throwError (loc, "array doesnt have such a field")
      -- TODO object handling in the future
    _ -> throwError (loc, "this doesn't have fields")

checkExpr (EApp loc ident exprs) = do
  t <- getType ident loc
  types <- mapM checkExpr exprs
  unless (isFunctional t) $ throwError (loc, "wrong type: not a function")
  let TCFun retT argTs = t
  unless (argTs == types) $ throwError (loc, "wrong argument type")
  return retT

checkExpr (EString _ string) = return TCStr
checkExpr (Neg loc expr) = do
  t <- checkExpr expr
  unless (t == TCInt) $ throwError (loc, "wrong negation type")
  return TCInt
checkExpr (Not loc expr) = do
  t <- checkExpr expr
  unless (t == TCBool ) $ throwError (loc, "wrong logic negation type")
  return TCBool

checkExpr (EMul loc exp1 _ exp2) = do
  t1 <- checkExpr exp1
  t2 <- checkExpr exp2
  unless (t1 == TCInt) $ throwError (loc, "wrong type of argument 1 for multiplying")
  unless (t2 == TCInt) $ throwError (loc, "wrong type of argument 2 for multiplying")
  return TCInt


checkExpr (EAdd loc exp1 (Plus loc2) exp2) = do
  t1 <- checkExpr exp1
  t2 <- checkExpr exp2
  unless (t1 == TCInt || t1 == TCStr) $ throwError (loc, "wrong type")
  unless (t2 == TCInt || t2 == TCStr) $ throwError (loc, "wrong type")
  unless (t1 == t2) $ throwError (loc, "wrong type")
  return t1

checkExpr (EAdd loc exp1 _ exp2) = do
  t1 <- checkExpr exp1
  t2 <- checkExpr exp2
  unless (t1 == TCInt) $ throwError (loc, "wrong type")
  unless (t2 == TCInt) $ throwError (loc, "wrong type")
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
     unless (t1 == TCInt) $ throwError (loc, "wrong type")
     unless (t2 == TCInt) $ throwError (loc, "wrong type")

   else do
     unless (t1 == t2) $ throwError (loc, "wrong type")
   return TCBool

checkExpr (EAnd loc exp1 exp2) = do
  t1 <- checkExpr exp1
  t2 <- checkExpr exp2
  unless (t1 == TCBool) $ throwError (loc, "wrong type")
  unless (t2 == TCBool) $ throwError (loc, "wrong type")
  return TCBool

checkExpr (EOr loc exp1 exp2) = do
  t1 <- checkExpr exp1
  t2 <- checkExpr exp2
  unless (t1 == TCBool) $ throwError (loc, "wrong type")
  unless (t2 == TCBool) $ throwError (loc, "wrong type")
  return TCBool

