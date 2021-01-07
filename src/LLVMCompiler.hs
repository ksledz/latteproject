
module LLVMCompiler where

import Data.Map (Map)
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Char as Char
import Control.Monad (void)
import Control.Monad.Reader
import Control.Monad.State
import Data.Void

import AbsLatte
import qualified AbsLatte as Latte


type Location = Maybe (Int, Int)
-- lol
data LLState = LLState (Map Int LLInstruction) (Map Int LLBlock) LLCurrent (Set String) (Map String (LLType, [LLType])) (Map String Int)
type LLInstruction = (Int, LLInsn)
data LLInsn = 	LLInsnAdd LLVal LLVal | 
		LLInsnSub LLVal LLVal |
		LLInsnNeg LLVal |
		LLInsnNot LLVal |
		LLInsnMul LLVal LLVal |
		LLInsnDiv LLVal LLVal |
		LLInsnMod LLVal LLVal |
		LLInsnAnd LLVal LLVal |
		LLInsnOr  LLVal LLVal |
		LLInsnEq  LLVal LLVal |
		LLInsnNe  LLVal LLVal |
		LLInsnLt  LLVal LLVal |
		LLInsnLe  LLVal LLVal |
		LLInsnGt  LLVal LLVal |
		LLInsnGe  LLVal LLVal |
		LLInsnCat LLVal LLVal |
		LLInsnCall String [(LLVal, LLType)] LLType |
		LLInsnPhi LLType |
		LLInsnArg Integer LLType 
data LLType = LLInt | LLStr | LLBool | LLVoid deriving Eq
data LLVal = LLReg Int | LLConstInt Integer | LLConstBool Bool | LLConstStr Int deriving Eq
-- params are: parent index and depth and end
data LLBlock = LLBlock Int Int LLEnd 
type LLJump = (Int, Map Int LLVal)
data LLEnd = LLVoidReturn | LLReturn (LLVal, LLType) | LLCond LLVal LLJump LLJump | LLJoin LLJump | LLOpen
data LLCurrent = LLCurrentBlock Int (Map String (LLVal, LLType)) | LLCurrentNone deriving Eq
type LLMonad a = State LLState a


findPhis_ [] m2 = []
findPhis_ ((k,(v,t)):tail) m2 = 
  let (v2, _) = (m2 Map.! k) in 
  if v==v2 then findPhis_ tail m2 else (k, t, v, v2):(findPhis_ tail m2)

findPhis :: (Map String (LLVal, LLType)) -> (Map String (LLVal, LLType)) -> [(String, LLType, LLVal, LLVal)]
findPhis m1 m2 = findPhis_ (Map.toList m1) m2

-- 
emitPhi :: Int -> (Map String (LLVal, LLType), Map Int LLVal, Map Int LLVal) -> (String, LLType, LLVal, LLVal) -> LLMonad(Map String (LLVal, LLType), Map Int LLVal, Map Int LLVal)

emitPhi block (mVars, mPhi1, mPhi2) (s, t, v1, v2) = do
  vp <- emitInsnToBlock block (LLInsnPhi t)
  let LLReg phi = vp
  return (Map.insert s (vp, t) mVars, Map.insert phi v1 mPhi1, Map.insert phi v2 mPhi2)

getVar :: String -> LLMonad (LLVal, LLType)
getVar a = do
  state <- get 
  let LLState _ _ (LLCurrentBlock _ m) _ _ _ = state
  let Just v = Map.lookup a m -- already type checked
  return v

getFunc :: String -> LLMonad (LLType, [LLType])
getFunc a = do
  state <- get
  let LLState _ _ _ _ m _ = state
  let Just v = Map.lookup a m
  return v

emitSimpleExpr :: LLInsn -> LLMonad LLVal
emitSimpleExpr = emitInsn

emitInsnToBlock :: Int -> LLInsn -> LLMonad LLVal
emitInsnToBlock block insn = do
  state <- get
  let LLState m1 a b c d e= state
  let index = Map.size m1
  let m = Map.insert index (block,insn) m1
  put (LLState m a b c d e)
  return (LLReg index)

emitInsn :: LLInsn -> LLMonad LLVal
emitInsn insn = do
  LLCurrentBlock block _ <- getCurrent
  emitInsnToBlock block insn

addLocalVar :: String -> LLMonad ()
addLocalVar v = do
  state <- get
  let LLState a b c s1 d e = state
  let s = Set.insert v s1
  put (LLState a b c s d e)
  return ()

getLocalVars :: LLMonad(Set String)
getLocalVars = do
  state <- get 
  let LLState _ _ _ s _ _= state
  return s

setLocalVars :: (Set String) -> LLMonad()
setLocalVars s = do
  state <- get
  let LLState a b c s1 d e = state
  put (LLState a b c s d e)
  return ()

setVar :: String -> (LLVal, LLType) -> LLMonad()
setVar s v = do
  state <- get
  let LLState a b (LLCurrentBlock i m1) c d e = state
  let m = Map.insert s v m1
  put (LLState a b (LLCurrentBlock i m) c d e)
  return ()

undefineVar :: (Map String (LLVal, LLType)) -> String -> (Map String (LLVal, LLType)) -> (Map String (LLVal, LLType))
undefineVar startVars var acc = case Map.lookup var startVars of 
  Nothing -> Map.delete var acc
  Just val -> Map.insert var val acc

getCurrent :: LLMonad LLCurrent
getCurrent = do
  state <- get
  let LLState _ _ c _ _ _ = state
  return c

setCurrent :: LLCurrent -> LLMonad ()
setCurrent c = do
  state <- get
  let LLState a b _ d e f = state
  put(LLState a b c d e f)
  return ()


startBlock :: Int -> LLMonad Int
startBlock parentIndex = do
  parentBlock <- getBlock parentIndex
  let LLBlock _ parentDepth _ = parentBlock
  let newBlock = LLBlock parentIndex (parentDepth+1) LLOpen
  state <- get
  let LLState a m1 b c d e = state
  let index = Map.size m1
  let m = Map.insert index newBlock m1
  put (LLState a m b c d e)
  return index

getBlock :: Int -> LLMonad LLBlock
getBlock index = do
  state <- get 
  let LLState _ m _ _ _ _ = state
  return (m Map.! index)

endBlock :: LLEnd -> LLMonad ()
endBlock end = do
  state <- get
  let LLState a m1 (LLCurrentBlock i _) c d e = state
  let currentBlock = m1 Map.! i
  let LLBlock parent depth _ = currentBlock
  let newBlock = LLBlock parent depth end
  let m = Map.insert i newBlock m1
  put (LLState a m LLCurrentNone c d e)
  return ()


makePhi :: (Map String (LLVal, LLType)) -> (Map String (LLVal, LLType)) -> String -> (Int, LLVal)

makePhi phiVars srcVars phi = 
  let (LLReg idx, _) = phiVars Map.! phi in (idx, fst (srcVars Map.! phi))

makePhis :: (Map String (LLVal, LLType)) -> (Set String) -> (Map String (LLVal, LLType)) -> (Map Int LLVal)
makePhis phiVars phis srcVars = Map.fromList(map (makePhi phiVars srcVars) (Set.toList phis))

emitLoopPhi :: Int -> (Map String (LLVal, LLType)) -> String -> LLMonad(Map String (LLVal, LLType))
emitLoopPhi block vars s = do
  let typ = snd $ vars Map.! s
  val <- emitInsnToBlock block (LLInsnPhi typ)
  return (Map.insert s (val, typ) vars)

translateWhile :: (Expr Location) -> (Stmt Location) -> (Set String) -> LLMonad()
translateWhile (ELitFalse _) _ _ = return()
translateWhile (ELitTrue loc)  stmt phiVars = do 
  state <- get  
  cur <- getCurrent
  let LLCurrentBlock curBlock curVars = cur
  loopBlock <- startBlock curBlock
  loopVars <- foldM (emitLoopPhi loopBlock) curVars phiVars
  let curPhis = makePhis loopVars phiVars curVars
  endBlock $ LLJoin (loopBlock, curPhis)
  setCurrent $ LLCurrentBlock loopBlock loopVars
  translateStmt stmt
  after <- getCurrent 
  case after of
    LLCurrentNone -> return () 
    LLCurrentBlock afterBlock afterVars -> do
      let actualPhiVars = Set.fromList $ map (\(a, _, _, _) -> a) (findPhis afterVars curVars)
      if Set.isSubsetOf actualPhiVars phiVars then do
        let afterPhis = makePhis loopVars phiVars afterVars
        endBlock $ LLJoin (loopBlock, afterPhis)
      else do
        put state
        translateWhile (ELitTrue loc) stmt (Set.union phiVars actualPhiVars)

translateWhile expr stmt phiVars = do
  state <- get  
  cur <- getCurrent
  let LLCurrentBlock curBlock curVars = cur
  loopBlock <- startBlock curBlock
  loopVars <- foldM (emitLoopPhi loopBlock) curVars phiVars
  let curPhis = makePhis loopVars phiVars curVars
  endBlock $ LLJoin (loopBlock, curPhis)
  setCurrent $ LLCurrentBlock loopBlock loopVars
  (cv, _)<-translateExpr expr
  LLCurrentBlock postCondBlock postCondVars <- getCurrent
  okBlock <- startBlock postCondBlock
  exitBlock <- startBlock postCondBlock
  endBlock (LLCond cv (okBlock, Map.empty) (exitBlock, Map.empty))
  setCurrent $ LLCurrentBlock okBlock postCondVars
  translateStmt stmt
  after <- getCurrent 
  case after of
    LLCurrentNone -> setCurrent $ LLCurrentBlock exitBlock postCondVars
    LLCurrentBlock afterBlock afterVars -> do
      let actualPhiVars = Set.fromList $ map (\(a, _, _, _) -> a) (findPhis afterVars curVars)
      if Set.isSubsetOf actualPhiVars phiVars then do
        let afterPhis = makePhis loopVars phiVars afterVars
        endBlock $ LLJoin (loopBlock, afterPhis)
        setCurrent $ LLCurrentBlock exitBlock postCondVars
      else do
        put state
        translateWhile expr stmt (Set.union phiVars actualPhiVars)

translateBlockStmt :: Stmt Location -> LLMonad()
translateBlockStmt s = do
  cur <- getCurrent
  if cur == LLCurrentNone then return () else translateStmt s

translateStmt :: Stmt Location -> LLMonad ()
translateBlock :: Block Location -> LLMonad ()
translateExpr :: Expr Location -> LLMonad (LLVal, LLType)
translateItem :: Item Location -> LLMonad()

translateExpr (EVar loc ident) = do
  let Ident s = ident 
  getVar s

translateExpr (ELitInt _ i) = return (LLConstInt i, LLInt)
translateExpr (ELitTrue _) = return (LLConstBool True, LLBool)
translateExpr (ELitFalse _) = return (LLConstBool False, LLBool)
translateExpr (EString _ string) = do 
  state <- get
  let LLState a b c d e m1 = state
  case Map.lookup string m1 of
    Nothing -> do
      let idx = Map.size m1
      let m = Map.insert string idx m1
      put (LLState a b c d e m)
      return (LLConstStr idx, LLStr)
    Just idx -> return (LLConstStr idx, LLStr)
translateExpr (Neg _ expr) = do
  (sv, _) <- translateExpr expr
  v <- emitSimpleExpr (LLInsnNeg sv)
  return (v, LLInt)

translateExpr (Not _ expr) = do
  (sv, _) <- translateExpr expr
  v <- emitSimpleExpr (LLInsnNot sv)
  return (v, LLBool)

translateExpr (EMul _ e1 (Times _) e2) = do
  (sv1, _) <- translateExpr e1
  (sv2, _) <- translateExpr e2
  v <- emitSimpleExpr (LLInsnMul sv1 sv2)
  return (v, LLInt)

translateExpr (EMul _ e1 (Div _)  e2) = do
  (sv1, _) <- translateExpr e1
  (sv2, _) <- translateExpr e2
  v <- emitSimpleExpr (LLInsnDiv sv1 sv2)
  return (v, LLInt)

translateExpr (EMul _ e1 (Mod _) e2) = do
  (sv1, _) <- translateExpr e1
  (sv2, _) <- translateExpr e2
  v <- emitSimpleExpr (LLInsnMod sv1 sv2)
  return (v, LLInt)

translateExpr (EAdd _ e1 (Plus _) e2) = do
  (sv1, st1) <- translateExpr e1
  (sv2, _) <- translateExpr e2
  v <- emitSimpleExpr (if st1 == LLInt then (LLInsnAdd sv1 sv2) else (LLInsnCat sv1 sv2))
  return (v, st1)

translateExpr (EAdd _ e1 (Minus _) e2) = do
  (sv1, _) <- translateExpr e1
  (sv2, _) <- translateExpr e2
  v <- emitSimpleExpr (LLInsnSub sv1 sv2)
  return (v, LLInt)

translateExpr (ERel _ e1 (LTH _) e2) = do
  (sv1, _) <- translateExpr e1
  (sv2, _) <- translateExpr e2
  v <- emitSimpleExpr (LLInsnLt sv1 sv2)
  return (v, LLBool)

translateExpr (ERel _ e1 (LE _) e2) = do
  (sv1, _) <- translateExpr e1
  (sv2, _) <- translateExpr e2
  v <- emitSimpleExpr (LLInsnLe sv1 sv2)
  return (v, LLBool)

translateExpr (ERel _ e1 (GTH _) e2) = do
  (sv1, _) <- translateExpr e1
  (sv2, _) <- translateExpr e2
  v <- emitSimpleExpr (LLInsnGt sv1 sv2)
  return (v, LLBool)

translateExpr (ERel _ e1 (GE _) e2) = do
  (sv1, _) <- translateExpr e1
  (sv2, _) <- translateExpr e2
  v <- emitSimpleExpr (LLInsnGe sv1 sv2)
  return (v, LLBool)

translateExpr (ERel _ e1 (EQU _) e2) = do
  (sv1, _) <- translateExpr e1
  (sv2, _) <- translateExpr e2
  v <- emitSimpleExpr (LLInsnEq sv1 sv2)
  return (v, LLBool)

translateExpr (ERel _ e1 (NE _) e2) = do
  (sv1, _) <- translateExpr e1
  (sv2, _) <- translateExpr e2
  v <- emitSimpleExpr (LLInsnNe sv1 sv2)
  return (v, LLBool)

translateExpr (EAnd _ e1 e2) = do
  (sv1, _) <- translateExpr e1
  -- what block r we in
  cur <- getCurrent
  let LLCurrentBlock curBlock curVars = cur

  joinBlock <- startBlock curBlock
  fv <- emitInsnToBlock joinBlock (LLInsnPhi LLBool)
  let LLReg phi = fv

  condBlock <- startBlock curBlock
  setCurrent(LLCurrentBlock condBlock curVars)  
  (sv2, _) <- translateExpr e2
  endBlock (LLJoin (joinBlock, (Map.singleton phi sv2)))

  setCurrent cur
  endBlock (LLCond sv1 (condBlock, Map.empty) (joinBlock, Map.singleton phi sv1))

  setCurrent(LLCurrentBlock joinBlock curVars)  
  return (fv, LLBool)

translateExpr (EOr _ e1 e2) = do
  (sv1, _) <- translateExpr e1
  -- what block r we in
  cur <- getCurrent
  let LLCurrentBlock curBlock curVars = cur

  joinBlock <- startBlock curBlock
  setCurrent(LLCurrentBlock joinBlock curVars)  
  fv <- emitInsn (LLInsnPhi LLBool)
  let LLReg phi = fv

  condBlock <- startBlock curBlock
  setCurrent(LLCurrentBlock condBlock curVars)  
  (sv2, _) <- translateExpr e2
  endBlock (LLJoin (joinBlock, (Map.singleton phi sv2)))

  setCurrent cur
  endBlock (LLCond sv1 (joinBlock, Map.singleton phi sv1) (condBlock, Map.empty))

  setCurrent(LLCurrentBlock joinBlock curVars)  
  return (fv, LLBool)

translateExpr (EApp _ i exprs) = do
  let Ident s = i
  args <- mapM translateExpr exprs 
  (rt, _ ) <- getFunc s 
  v <- emitInsn (LLInsnCall s args rt)
  return (v, rt)

translateStmt (Empty _) = return ()
translateStmt (BStmt _ b) = translateBlock b
translateStmt (Decl _ t i) = do
  mapM_ translateItem i

translateStmt (Ass _ ident expr) = do
  let Ident s = ident 
  val <- translateExpr expr 
  setVar s val

translateStmt (Incr _ ident) = do
  let Ident s = ident
  (val, typ) <- getVar s 
  nval <- emitSimpleExpr(LLInsnAdd val (LLConstInt 1))
  setVar s (nval, LLInt)

translateStmt (Decr _ ident) = do
  let Ident s = ident
  (val, typ) <- getVar s 
  nval <- emitSimpleExpr(LLInsnAdd val (LLConstInt (-1)))
  setVar s (nval, LLInt)

translateStmt (SExp _ expr) = do 
  translateExpr expr
  return ()

-- TODO while
translateStmt (Cond _ expr stmt) = do
  (sv, _) <- translateExpr expr
  case sv of
    LLConstBool True -> translateStmt stmt
    LLConstBool False -> return ()
    _ -> do
      cur <- getCurrent
      let LLCurrentBlock curBlock curVars = cur
      condBlock <- startBlock curBlock
      setCurrent (LLCurrentBlock condBlock curVars)
      translateStmt stmt
      cond <- getCurrent
      joinBlock <- startBlock curBlock
      case cond of 
        LLCurrentNone -> do
          setCurrent cur
          endBlock (LLCond sv (condBlock, Map.empty) (joinBlock, Map.empty))
          setCurrent(LLCurrentBlock joinBlock curVars)
        LLCurrentBlock finalCondBlock condVars -> do
          let phis = findPhis condVars curVars
          (joinVars, condPhis, curPhis) <- foldM (emitPhi joinBlock) (curVars, Map.empty, Map.empty) phis
          
          endBlock (LLJoin (joinBlock, condPhis))
          setCurrent cur
          endBlock (LLCond sv (condBlock, Map.empty) (joinBlock, curPhis))
          setCurrent(LLCurrentBlock joinBlock joinVars)

translateStmt (CondElse _ expr stmt1 stmt2) = do
  (sv, _) <- translateExpr expr
  case sv of
    LLConstBool True -> translateStmt stmt1
    LLConstBool False -> translateStmt stmt2
    _ -> do
      cur <- getCurrent
      let LLCurrentBlock curBlock curVars = cur
      condBlock1 <- startBlock curBlock
      setCurrent (LLCurrentBlock condBlock1 curVars)
      translateStmt stmt1
      cond1 <- getCurrent
      condBlock2 <- startBlock curBlock
      setCurrent (LLCurrentBlock condBlock2 curVars)
      translateStmt stmt2
      cond2 <- getCurrent
      setCurrent cur
      endBlock (LLCond sv (condBlock1, Map.empty) (condBlock2, Map.empty))
      case (cond1, cond2) of 
        (LLCurrentNone, LLCurrentNone) -> return ()
        (LLCurrentNone, LLCurrentBlock finalCond2Block condVars2) -> setCurrent cond2
        (LLCurrentBlock finalCond1Block condVars1, LLCurrentNone) -> setCurrent cond1
        (LLCurrentBlock finalCond1Block condVars1, LLCurrentBlock finalCond2Block condVars2) -> do
       
          joinBlock <- startBlock curBlock
          let phis = findPhis condVars1 condVars2
          (joinVars, condPhis1, condPhis2) <- foldM (emitPhi joinBlock) (curVars, Map.empty, Map.empty) phis
          setCurrent cond1
          endBlock (LLJoin (joinBlock, condPhis1))
          setCurrent cond2
          endBlock (LLJoin (joinBlock, condPhis2))
          setCurrent(LLCurrentBlock joinBlock joinVars)
translateStmt (While _ expr stmt) = translateWhile expr stmt Set.empty

translateStmt (Ret _ expr) = do
  v <- translateExpr expr
  endBlock (LLReturn v)

translateStmt (VRet _) = do
  endBlock (LLVoidReturn)

translateItem (NoInit _ ident) = do
  let Ident s = ident 
  addLocalVar s

translateItem (Init _ ident expr) = do
  let Ident s = ident
  val <- translateExpr expr
  addLocalVar s 
  setVar s val

-- TODO
translateBlock (Block _ stmts) = do
  cur <- getCurrent 
  let LLCurrentBlock _ startVars = cur
  startLocalVars <- getLocalVars
  setLocalVars Set.empty
  mapM_ translateBlockStmt stmts
  after <- getCurrent
  endLocalVars <- getLocalVars
  setLocalVars startLocalVars
  case after of
    LLCurrentNone -> return ()
    LLCurrentBlock endBlock endVars -> do
      let finalVars = Set.foldr (undefineVar startVars) endVars endLocalVars
      setCurrent $ LLCurrentBlock endBlock finalVars

