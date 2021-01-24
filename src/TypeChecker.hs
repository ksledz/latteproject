module TypeChecker (checkTypes) where

import Data.Map (Map, (!))
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Set (Set)
import Control.Monad.Reader
import Control.Monad.Except

import AbsLatte
import qualified AbsLatte as Latte

data TCType = TCInt | TCStr | TCBool | TCVoid | TCFun TCType [TCType] | TCArray TCType | TCObject Ident deriving Eq
type Location = Maybe (Int, Int)
type StructDef = (Set Ident, Map Ident TCType)
type TCState = (Map Ident TCType, TCType, Map Ident StructDef, Maybe Ident)
type TypeMonad a = ReaderT TCState (Except (Location, String)) a

runTypeMonad :: TypeMonad a -> Either String a
runTypeMonad a = case runExcept $ runReaderT a  (Map.empty, TCVoid, Map.empty, Nothing) of
  Right x -> Right x
  Left ((Just (l, c)), s) -> Left ("type error at line " ++ show l ++ ", column " ++ show c ++ ": "++ s)
  Left (Nothing, s) -> Left s

getSymbols :: TCState -> Map Ident TCType    
getSymbols (a, _, _,  _) = a
getReturnType :: TCState -> TCType
getReturnType(_, a, _, _) = a
getStructs :: TCState -> Map Ident StructDef
getStructs(_, _, a, _) = a
getCurrentStruct ::TCState -> Maybe Ident
getCurrentStruct (_, _, _, a) = a

transformSymbols :: (Map Ident TCType -> Map Ident TCType) -> TCState -> TCState
transformSymbols fun (a,b,c,d) = (fun a, b, c, d)
setReturnType :: TCType -> TCState -> TCState
setReturnType b (a, _, c, d) = (a, b, c, d)
setCurrentStruct :: Maybe Ident -> TCState -> TCState 
setCurrentStruct d (a, b, c, _)  = (a, b, c, d)

getStruct :: Location -> Ident -> TypeMonad StructDef
getStruct loc ident = do
  structs <- asks getStructs
  case Map.lookup ident structs of
    Nothing -> throwError (loc, "unknown class")
    Just sd -> return sd

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
  structDefs <- makeStructDefs Map.empty list
  local (const (fnTypes, TCVoid, structDefs, Nothing)) (mapM_ checkTopDef list) 

makeStructDefs :: Map Ident StructDef -> [TopDef Location] -> TypeMonad (Map Ident StructDef)
makeStructDefs m [] = return m
makeStructDefs m (ClassDef loc ident items:tail) = do
  when (Map.member ident m) $ throwError (loc, "redefined class")
  makeStructDefs (Map.insert ident (Set.empty, makeStructDef Map.empty items) m) tail
makeStructDefs m (ClassEDef loc ident base items:tail) = do
  when (Map.member ident m) $ throwError (loc, "redefined class")
  case Map.lookup base m of
    Nothing -> throwError (loc, "unknown base class")
    Just (bases, defs) -> makeStructDefs (Map.insert ident (Set.insert base bases, makeStructDef defs items) m) tail
makeStructDefs m (_:tail) = makeStructDefs m tail

makeStructDef :: Map Ident TCType -> [ClassItem Location] -> Map Ident TCType
makeStructDef m [] = m
makeStructDef m (head:tail) = let (k, v) = getClassItemType head in makeStructDef (Map.insert k v m) tail

getClassItemType :: ClassItem Location -> (Ident, TCType)
getClassItemType (FieldDef _ t ident) = (ident, convertType t)
getClassItemType (MethodDef _ t ident arg _) = (ident, TCFun (convertType t) (unpackTypes arg))

getTopTypes ::  [TopDef a] -> [(Ident, TCType)]
getTopTypes [] = []
getTopTypes (FnDef _ t ident arg _:tail) = (ident, TCFun (convertType t) (unpackTypes arg)):getTopTypes tail
getTopTypes (_:tail) = getTopTypes tail

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
convertType (Latte.Struct _ i) =  TCObject i

checkType :: Bool -> Type Location -> TypeMonad TCType
checkType _ (Latte.Int _) = return TCInt
checkType _ (Latte.Str _) = return TCStr
checkType _ (Latte.Bool _) = return TCBool
checkType voidOk (Latte.Void loc) = do
  if voidOk 
    then return TCVoid
    else throwError (loc, "this place cannot be a V O I D")
checkType _ (Latte.Arr _ t) = do
  tt <- checkType False  t
  return $ TCArray tt
checkType _ (Latte.Struct loc i) = do
  getStruct loc i
  return $ TCObject i

checkCovariantTypes :: Location -> TCType -> TCType -> TypeMonad ()
checkCovariantTypes loc t1 t2 = do
  if t1 == t2 then return () else do
    case (t1, t2) of
      (TCObject i1, TCObject i2) -> do
        (b2, _) <- getStruct loc i2
        unless (Set.member i1 b2) $ throwError (loc, "assigning incompatible class types")
      _ -> throwError (loc, "assigning incompatible types")

makePair :: Arg Location -> TypeMonad (Ident, TCType)
makePair (Arg _ t i) = do
  at <- checkType False t
  return (i, at)

checkTopDef :: TopDef Location -> TypeMonad ()

checkTopDef (FnDef loc t ident args block) = do
  argPairs <- mapM makePair args
  let newVars = Map.fromList argPairs
  unless ((Map.size newVars) == length(args)) $ throwError (loc, "repeating identifiers")
  rt <- checkType True t
  res <- local ((transformSymbols (Map.union newVars)).(setReturnType rt)) $ checkBlock block Set.empty
  case t of
    Latte.Void _ -> return ()
    _ -> unless res $ throwError (loc, "missing return")

checkTopDef (ClassDef loc ident items) = do
  let newVars = Map.fromList (map getClassItemType items)
  unless ((Map.size newVars) == length(items)) $ throwError (loc, "repeating fields/methods")
  local ((transformSymbols (Map.union newVars)).(setCurrentStruct $ Just ident)) $ mapM_ checkClassItem items

checkTopDef (ClassEDef loc ident base items) = do
  let curVars = map getClassItemType items
  unless ((Map.size (Map.fromList curVars)) == length(items)) $ throwError (loc, "repeating fields/methods")
  (_, baseVars) <- getStruct loc base
  mapM_ (checkSubClassItem loc baseVars) curVars
  (_, newVars) <- getStruct loc ident
  local ((transformSymbols (Map.union newVars)).(setCurrentStruct $ Just ident)) $ mapM_ checkClassItem items

checkSubClassItem :: Location -> Map Ident TCType -> (Ident, TCType) -> TypeMonad ()
checkSubClassItem loc bMap (ident, t) = do
  case Map.lookup ident bMap of
    Nothing -> return ()
    Just bt -> do
      unless (t == bt) $ throwError (loc, "field/method collision with base class")
      unless (isFunctional t) $ throwError (loc, "field redeclared from base class")

checkClassItem :: ClassItem Location -> TypeMonad ()
checkClassItem (FieldDef _ t _) = do
  checkType False  t
  return ()

checkClassItem (MethodDef loc t ident args block) = do
  argPairs <- mapM makePair args
  let newVars = Map.fromList argPairs
  unless ((Map.size newVars) == length(args)) $ throwError (loc, "repeating identifiers")
  rt <- checkType True t
  res <- local ((transformSymbols (Map.union newVars)).(setReturnType rt)) $ checkBlock block Set.empty
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
  tt <- checkType False t
  let newVars = Map.fromList (zip (map getIdent item) (repeat tt))
  unless ((Map.size newVars) == length(item)) $ throwError (loc, "repeating identifiers")
  checkStmt stmt
  when (any (\i -> Set.member(getIdent i) lVars) item ) $ throwError (loc, "redefined variable")
  let newLVars = Set.union lVars (Set.fromList (map getIdent item))
  local (transformSymbols (Map.union newVars) ) ( checkBlock (Block loc tail) newLVars)

checkBlock(Block loc (head:tail)) lVars = do
  res1 <- checkStmt head
  res2 <- checkBlock (Block loc tail) lVars
  return (res1 || res2)


getType :: Ident -> Location -> TypeMonad TCType
getType i loc = do
  r <-asks  getSymbols
  let Ident s = i
  unless (Map.member i r) $ throwError (loc, "undefined identifier: " ++ s)
  return (r ! i)

checkStmt :: Stmt Location -> TypeMonad Bool
checkStmt (Empty _) = return False
checkStmt (BStmt _ b) = checkBlock b Set.empty
checkStmt (Decl _ t i) = do 
  tt <- checkType False  t
  mapM_ (checkItem tt) i
  return False
checkStmt (Ass loc lval expr) = do
  t <- checkExpr expr
  ti <- checkLValue lval loc
  checkCovariantTypes loc ti t
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
  tret <- asks getReturnType
  checkCovariantTypes loc tret t
  return True

checkStmt (VRet loc) = do
  t <- asks getReturnType
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
  t1 <- checkType False t
  t2 <- checkExpr expr
  unless (t2 == TCArray t1) $ throwError (loc, "wrong type of loop variable")
  local (transformSymbols (Map.insert ident t1) ) $ checkStmt stmt



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
  checkCovariantTypes loc t t1

isFunctional :: TCType -> Bool
isFunctional (TCFun _ _) = True
isFunctional _ = False

checkExpr :: Expr Location -> TypeMonad TCType
checkExpr (EVar loc ident) = getType ident loc
checkExpr (ELitInt _ integer) = return TCInt
checkExpr (ELitTrue _) = return TCBool
checkExpr (ELitFalse _) = return TCBool
checkExpr (EArr loc t expr) = do
  t1 <- checkType False t
  t2 <- checkExpr expr
  unless (t2 == TCInt) $ throwError (loc, "wrong array length type")
  return $ TCArray t1

checkExpr (EIndex loc e1 e2) = do
  t1 <- checkExpr e1
  t2 <- checkExpr e2
  unless (t2 == TCInt) $ throwError (loc, "wrong array index type")
  case t1 of
    TCArray t -> return t
    _ -> throwError (loc, "sweet jesus, pooh! that's not an array-able type")

checkExpr (EField loc expr ident) = do
  t1 <- checkExpr expr
  let Ident s = ident
  case t1 of
    TCArray _ -> do
      if (s == "length") then return TCInt else throwError (loc, "array doesnt have such a field")
    TCObject i -> do
      (_, sd) <- getStruct loc i
      case Map.lookup ident sd of
        Nothing -> throwError (loc, "unknown field")
        Just t -> return t
    _ -> throwError (loc, "this doesn't have fields")

checkExpr (EObject loc ident) = do
  getStruct loc ident
  return $ TCObject ident

checkExpr (ENull loc t) = do
  checkType False t

checkExpr (EApp loc ident exprs) = do
  t <- getType ident loc
  types <- mapM checkExpr exprs
  unless (isFunctional t) $ throwError (loc, "wrong type: not a function")
  let TCFun retT argTs = t
  mapM_ (uncurry (checkCovariantTypes loc)) (zip argTs types)
  return retT

checkExpr (EMthdApp loc expr ident exprs) = do
  t1 <- checkExpr expr
  case t1 of
    TCObject i -> do
      (_, sd) <- getStruct loc i
      case Map.lookup ident sd of
        Nothing -> throwError (loc, "unknown method")
        Just t -> do
          types <- mapM checkExpr exprs
          unless (isFunctional t) $ throwError (loc, "wrong type: not a method")
          let TCFun retT argTs = t
          mapM_ (uncurry (checkCovariantTypes loc)) (zip argTs types)
          return retT
    _ -> throwError (loc, "this doesn't have methods")

checkExpr (ESelf loc) = do
  cs <- asks getCurrentStruct
  case cs of
    Nothing -> throwError (loc, "self used outside of method")
    Just i -> return $ TCObject i

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

