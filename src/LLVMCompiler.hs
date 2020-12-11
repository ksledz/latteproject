
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
data Loc = LocReg Register
  | LocAddress Register
  | LLConst Int
data LLArg = LLArg LLType Ident
data LLVMRep =
  LLFunc LLType Ident [LLArg] [LLBlock]
  | LLReturn (Maybe (LLType, Loc))
  | LLCall Loc LLType Ident [(LLType, Loc)]
  | LLInternalConst Register Int String
  | LLSub Loc Loc Loc
  | LLSubI1 Loc Loc Loc
  | LLAdd Loc Loc Loc
  | LLMul Loc Loc Loc
  | LLDiv Loc Loc Loc
  | LLMod Loc Loc Loc
  | LLLTH Loc Loc Loc
  | LLLE Loc Loc Loc
  | LLGTH Loc Loc Loc
  | LLGE Loc Loc Loc
  | LLEQU Loc Loc Loc
  | LLNE Loc Loc Loc
  | LLAnd Loc Loc Loc
  | LLOr Loc Loc Loc
  | LLAloca LLType Loc
  | LLStore LLType Loc Loc
data LLType =
  I8 | I32 | I1 | Void | LLStar LLType
type LLVMonad a =
  ReaderT (Map Ident Loc, Map Ident Type) (StateT Int (Writer [LLVMRep])) a
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
-- TODO #5 na sam koniec, matchowanie

programToLLVM :: Program -> String
programToLLVM (Program l) = generateCode (runLLVMonad (mapM_ topDefToLLVM l) )

swapArgs :: Arg -> (Ident, Type)
swapArgs (Arg t i) = (i, t)
getIdentLoc :: Arg -> LLVMonad (Ident, Loc)
getIdentLoc (Arg t i) = do
  reg <- freshRegister
  tell [LLAlloca (typeToLLType t), (LocAddress reg)]
  return (i, LocAddress reg)

topDefToLLVM :: TopDef -> LLVMonad ()
topDefToLLVM (FnDef t ident args block) = do
  let tempList2 = map swapArgs args
  tempList1 <- mapM getIdentLoc args
  let tempMap1 = fromList tempList1
      tempMap2 = fromList tempList2
  local (\x -> (Map.union tempMap1 (fst x), Map.union tempMap2 (snd x))) $
    censor ((:[]) . LLFunc (typeToLLType t) ident (map argToLLArg args)) $ blockToLLVM block

getArgsList1 :: Type -> [Item] -> LLVMonad([(Ident, Loc)])
getArgsList1 t [] = []
getArgsList1 t (NoInit i:tail) = do
  reg <- freshRegister
  tell [LLAlloca (typeToLLType t), (LocAddress reg)]
  generateDefaultConstructor (typeToLLType t) (LocAddress reg)
  list <- getArgsList1 t tail
  return ((i, LocAddress reg):list)


getArgsList1 t (Init i e:tail) = do
  reg <- freshRegister
  tell [LLAlloca (typeToLLType t), (LocAddress reg)]
  (_, l) <- exprToLLVM e
  assign l (LocAddress reg) t
  list <- getArgsList1 t tail
  return ((i, LocAddress reg):list)
generateDefaultConstructor :: LLType -> Loc -> LLVMonad ()

generateDefaultConstructor I32 loc = tell [LLStore I32 (LLConst 0) loc]
generateDefaultConstructor I1 loc = tell [LLStore I1 (LLConst 0) loc]
generateDefaultConstructor (LLStar I8) loc = do
  reg <- freshRegister
  tell [LLCall (LocAddress reg) (LLStar I8) (Ident "malloc") [(I32, LLConst 1), (I32, LLConst 1]]
  assign loc (LocAddress reg) (LLStar I8)

getArgsList2 :: Type -> [Item] -> [(Ident, Type)]
getArgsList2 t [] = []
getArgsList2 t (NoInit i:tail) = [(i, t):(getArgsList2 t tail)]
getArgsList2 t (Init i _:tail) = [(i, t):(getArgsList2 t tail)]
blockToLLVM :: Block -> LLVMonad ()
blockToLLVM (Block (Decl t items):tail) = do
  let tempList2 = getArgsList2 t items
  tempList1 <- getArgsList1 t items
  let tempMap1 = fromList tempList1
      tempMap2 = fromList tempList2
  local (\x -> (Map.union tempMap1 (fst x), Map.union tempMap2 (snd x))) $ blockToLLVM block

blockToLLVM (Block (h:t)) = do
  stmtToLLVM h
  blockToLLVM (Block t)

blockToLLVM (Block []) = return ()
stmtToLLVM :: Stmt -> LLVMonad ()
stmtToLLVM Empty = return ()
stmtToLLVM VRet = tell [LLReturn Nothing]
stmtToLLVM (Ret e) = do
  loc <- exprToLLVM e
  tell [LLReturn (Just loc)]
stmtToLLVM (Bstmt b) = blockToLLVM b
stmtToLLVM (Ass i e) = do
  (map1, map2) <- ask
  let l = map1 ! i
      t = map2 ! i
  (_, exprl) <- exprToLLVM e
  assign l exprl t


stmtToLLVM Cond expr stmt --TODO #4 generacja labelów i blocków
stmtToLLVM CondElse expr stmt --TODO generacja labelów i blocków
stmtToLLVM While expr stmt --TODO generacja labelów i blocków
stmtToLLVM Incr i = return () -- TODO ???
stmtToLLVM Decr i = return () -- TODO ???
stmtToLLVM expr = exprToLLVM expr

exprToLLVM :: Expr -> LLVMonad (LLType, Loc)
exprToLLVM (EVar i) = getLocType i
exprToLLVM (ELitInt i) = return (I32, LLConst i)
exprToLLVM ELitTrue = return (I1, LLConst 1)
exprToLLVM ELitFalse = return (I1, LLConst 0)
exprToLLVM (EApp i exprs) = do
  m <- mapM exprToLLVM exprs
  reg <- freshRegister
  t <- getType i
  tell [LLCall (LocReg reg) t i m]
  return (t, LocReg reg)

exprToLLVM (EString s) = do
  reg <- freshRegister
  let i = length s
  tell [LLInternalConst reg i s]
  return (LLStar I8, LocAddress reg)


exprToLLVM EArr t expr = do
  reg  <- freshRegister
  (t1, l) <- exprToLLVm expr
  tell [LLCall (LocAddress reg) (LLStar (typeToLLType t)) (Ident "malloc") [(t1, l), (I32, LLConst (width t)]]
  return (LLStar (typeToLLType t), (LocAddress reg))

exprToLLVM Neg expr = do
  reg <- freshRegister
  (t, l) <- exprToLLVM expr
  tell [LLSub (LocReg reg) (LLConst 0) l]
  return (I32, (LocReg reg))

exprToLLVM Not expr = do
  reg <- freshRegister
  (t, l) <- exprToLLVM expr
  tell [LLSubI1 (LocReg reg) (LLConst 1) l]
  return (I1, (LocReg reg))

exprToLLVM (EMul expr1 op expr2) = do
  reg <- freshRegister
  (t1, l1) <- exprToLLVM expr1
  (t2, l2) <- exprToLLVM expr2
  tell [mulOpToFn op (LocReg reg) l1 l2]
  return (I32, (LocReg reg))

exprToLLVM (EAdd expr1 op expr2) = do
  reg <- freshRegister
  (t1, l1) <- exprToLLVM expr1
  (t2, l2) <- exprToLLVM expr2
  tell [addOpToFn op (LocReg reg) l1 l2]
  return (I32, (LocReg reg))

exprToLLVM (ERel expr1 op expr2) = do
  reg <- freshRegister
  (t1, l1) <- exprToLLVM expr1
  (t2, l2) <- exprToLLVM expr2
  tell [relOpToFn op (LocReg reg) l1 l2 ]
  return (I1, (LocReg reg))


exprToLLVM (EAnd expr1 expr2) = do
  reg <- freshRegister
  (t1, l1) <- exprToLLVM expr1
  (t2, l2) <- exprToLLVM expr2
  tell [LLAnd (LocReg reg) l1 l2]
  return (I1, (LocReg reg))
exprToLLVM (EOr expr1 expr2) = do
  reg <- freshRegister
  (t1, l1) <- exprToLLVM expr1
  (t2, l2) <- exprToLLVM expr2
  tell [LLOr (LocReg reg) l1 l2]
  return (I1, (LocReg reg))


mulOpToFn :: MulOp -> Loc -> Loc -> Loc -> LLVMRep
opToFn Times = LLMul
opToFn Div = LLDiv
opToFn Mod = LLMod
AddOpToFn :: AddOp -> Loc -> Loc -> Loc -> LLVMRep
opToFn Plus = LLAdd
opToFn Minus = LLSub
RelOpToFn :: RelOp -> Loc -> Loc -> Loc -> LLVMRep
opToFn LTH = LLLTH
opToFn LE = LLLE
opToFn GTH = LLGTH
opToFn GE = LLGE
opToFn EQU = LLEQU
opToFn NE = LLNE

getLocType :: Ident -> LLVMonad(LLType, Loc)
getLocType i = do
  (map1, map2) <- ask
  let l = map1 ! i
      t = map2 ! i
  return (t, l)
getType :: Ident -> LLVMonad(LLType)
getType i = do
  map2 <- asks snd
  return (map2 ! i)


freshRegister :: LLVMonad Register
freshRegister = do
  oldRegister <- get
  put $ oldRegister + 1
  return $ "%" ++ show (oldRegister + 1)

assign :: Loc -> Loc -> LLType -> LLVMonad ()
assign = undefined -- TODO #koniec

width ::LLType -> Int
width I8 = 1
width I32 = 4
width I1 = 1
width LLStar t = 8 -- ?
