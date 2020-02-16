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

-- TODO #1 jest 3 w nocy kurwa

exprToLLVM EArr t expr = do
  reg  <- freshRegister
  (t1, l) <- exprToLLVm expr
  tell [LLCall (LocAddress reg) LLStar (typeToLLType t) (Ident "malloc") [(t1, l), (I32, LLConst (width t)]]
  return (LLStar (typeToLLType t), (LocAddress reg))

exprToLLVM Neg expr = do
  reg <- freshRegister
  (t, l) <- exprToLLVM expr
  tell [LLSub (LocReg reg) (LLConst 0) l]
  return (I32, (LocReg reg))

exprToLLVM (EMul expr1 op expr2) = do
  reg <- freshRegister
  (t1, l1) <- exprToLLVM expr1
  (t2, l2) <- exprToLLVM expr2
  tell [mulOpToFn(op (LocReg reg) l1 l2)]
  return (I32, (LocReg reg))

exprToLLVM (EAdd expr1 op expr2) = do
  reg <- freshRegister
  (t1, l1) <- exprToLLVM expr1
  (t2, l2) <- exprToLLVM expr2
  tell [addOpToFn(op (LocReg reg) l1 l2)]
  return (I32, (LocReg reg))

exprToLLVM (ERel expr1 op expr2) = do
  reg <- freshRegister
  (t1, l1) <- exprToLLVM expr1
  (t2, l2) <- exprToLLVM expr2
  tell [relOpToFn(op (LocReg reg) l1 l2)]
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


width :: LLType -> Int
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
  return $ "%XD" ++ show (oldRegister + 1)

assign :: Loc -> Loc -> LLType -> LLVMonad ()

assign = undefined -- TODO #2

