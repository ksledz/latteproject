
module Main where
import System.Environment(getArgs)
import Text.Printf
import Data.Map (Map)
import Data.Set (Set)
import Data.List 
import Data.Word (Word8)
import Data.ByteString (ByteString)
import Data.Text.Encoding (encodeUtf8)
import qualified Data.Text as T
import qualified Data.ByteString as ByteString
import qualified Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Char as Char
import Control.Monad (void)
import Control.Monad.Reader
import Control.Monad.State
import Data.Void
import System.Process
import System.Exit
import System.IO

import AbsLatte
import LexLatte
import ParLatte
import TypeChecker
import qualified AbsLatte as Latte

import ErrM

type Location = Maybe (Int, Int)
-- lol
data LLState = LLState (Map Int LLInstruction) (Map Int LLBlock) LLCurrent LLVarsUndo LLFuncMap LLStringMap (Map LLInsn Int) LLStructMap (Maybe String) LLType
type LLVarsUndo = Map String (Maybe (LLVal, LLType))
type LLFuncMap = Map String (LLType, [LLType])
type LLStringMap = Map String (Int, Int, ByteString)
type LLVarMap = Map String (LLVal, LLType)
type LLStructMap = Map String LLStructDef
type LLStructDef = (LLFieldMap, LLMethodMap, Map Int LLType, Map Int (LLType, [LLType], String, String))
type LLFieldMap = Map String (Int, LLType)
type LLMethodMap = Map String (Int, LLType, [LLType], String)
type LLInstruction = (Int, LLInsn)
data LLInsn = LLInsnAdd LLVal LLVal |
        LLInsnSub LLVal LLVal |
        LLInsnNeg LLVal |
        LLInsnNot LLVal |
        LLInsnMul LLVal LLVal |
        LLInsnDiv LLVal LLVal |
        LLInsnMod LLVal LLVal |
        LLInsnEq  LLType LLVal LLVal |
        LLInsnNe  LLType LLVal LLVal |
        LLInsnLt  LLVal LLVal |
        LLInsnLe  LLVal LLVal |
        LLInsnGt  LLVal LLVal |
        LLInsnGe  LLVal LLVal |
        LLInsnCat LLVal LLVal |
        LLInsnCall String [(LLVal, LLType)] LLType |
        LLInsnArrayLoad LLType LLVal LLVal |
        LLInsnArrayStore LLType LLVal LLVal LLVal |
        LLInsnArrayNew LLType LLVal |
        LLInsnArrayLength LLType LLVal |
        LLInsnObjectNew String |
        LLInsnObjectLoad String LLType LLVal Int |
        LLInsnObjectStore String LLType LLVal Int LLVal |
        LLInsnObjectCall String LLVal Int [(LLVal, LLType)] LLType |
        LLInsnObjectCast LLType LLType LLVal |
        LLInsnPhi LLType deriving (Eq, Ord, Show)

data LLType = LLInt | LLStr | LLBool | LLVoid | LLArray LLType | LLObject String deriving (Eq, Ord, Show)
data LLVal = LLReg Int | LLConstInt Integer | LLConstBool Bool | LLConstStr Int Int | LLArg Int | LLSelf |LLNull deriving (Eq, Ord, Show)
-- params are: parent index and depth and end
data LLBlock = LLBlock Int Int LLEnd 
type LLJump = (Int, Map Int LLVal)
data LLEnd = LLVoidReturn | LLReturn (LLVal, LLType) | LLCond LLVal LLJump LLJump | LLJoin LLJump | LLOpen
data LLCurrent = LLCurrentBlock Int LLVarMap | LLCurrentNone deriving Eq
type LLMonad a = State LLState a

data TopState = TopState LLFuncMap LLStructMap LLStringMap
type TopMonad a = State TopState a


unescapeTail :: String -> String
unescapeTail "\"" = ""
unescapeTail ('\\':'\\':t) = '\\':(unescapeTail t)
unescapeTail ('\\':'"':t) = '\"':(unescapeTail t)
unescapeTail ('\\':'t':t) = '\t':(unescapeTail t)
unescapeTail ('\\':'r':t) = '\r':(unescapeTail t)
unescapeTail ('\\':'n':t) = '\n':(unescapeTail t)
unescapeTail ('\\':'f':t) = '\f':(unescapeTail t)
unescapeTail ('\\':_:t) = undefined
unescapeTail (h:t) = h:(unescapeTail t)

unescape :: String -> String
unescape ('\"':t) = unescapeTail t


findPhis_ [] m2 = []
findPhis_ ((k,(v,t)):tail) m2 = 
  let (v2, _) = (m2 Map.! k) in 
  if v==v2 then findPhis_ tail m2 else (k, t, v, v2):(findPhis_ tail m2)

findPhis :: LLVarMap -> LLVarMap -> [(String, LLType, LLVal, LLVal)]
findPhis m1 m2 = findPhis_ (Map.toList m1) m2

emitPhi :: Int -> (LLVarMap, Map Int LLVal, Map Int LLVal) -> (String, LLType, LLVal, LLVal) -> LLMonad (LLVarMap, Map Int LLVal, Map Int LLVal)

emitPhi block (mVars, mPhi1, mPhi2) (s, t, v1, v2) = do
  vp <- translateInsnToBlock block (LLInsnPhi t)
  let LLReg phi = vp
  return (Map.insert s (vp, t) mVars, Map.insert phi v1 mPhi1, Map.insert phi v2 mPhi2)

getVar :: String -> LLMonad (LLVal, LLType)
getVar a = do
  state <- get
  let LLState _ _ (LLCurrentBlock _ m) _ _ _ _ _ _ _= state
  case Map.lookup a m of
    Just v -> return v
    Nothing -> do
      st <- getSelfType
      let Just sn = st
      (fm, _, _, _) <- getStructDef sn
      let (idx, t) = fm Map.! a
      v <- translateInsn (LLInsnObjectLoad sn t LLSelf idx)
      return (v, t)

getFunc :: String -> LLMonad (Maybe (LLType, [LLType]))
getFunc a = do
  state <- get
  let LLState _ _ _ _ m _ _ _ _ _= state
  return $ Map.lookup a m

blockLCA :: Int -> Int -> LLMonad(Int) 
blockLCA b1 b2 = do
  LLBlock parent1 depth1 _ <- getBlock b1
  LLBlock parent2 depth2 _ <- getBlock b2
  if b1 == b2 then return b1 else
    if depth2 > depth1
      then blockLCA parent2 b1
      else if depth1 > depth2
        then blockLCA parent1 b2
        else blockLCA parent1 parent2

-- common subexprs optimalization
translateSimpleExpr :: LLInsn -> LLMonad LLVal
translateSimpleExpr insn = do
  state <- get
  let LLState insns a b c d e subExprs f g h = state
  case Map.lookup insn subExprs of
    Just idx -> do
      cur <- getCurrent
      let LLCurrentBlock curBlock _ = cur
      let (otherBlock, _) = insns Map.! idx
      lcaBlock <- blockLCA curBlock otherBlock
      let newInsns = Map.insert idx (lcaBlock, insn) insns
      put (LLState newInsns a b c d e subExprs f g h)
      return(LLReg idx)
    Nothing -> do
      val <- translateInsn insn
      let LLReg idx = val
      let newSubExprs = Map.insert insn idx subExprs
      state <- get
      let LLState insns a b c d e _ f g h = state
      put (LLState insns a b c d e newSubExprs f g h)
      return(val)

translateInsnToBlock :: Int -> LLInsn -> LLMonad LLVal
translateInsnToBlock block insn = do
  state <- get
  let LLState m1 a b c d e f g h i = state
  let index = Map.size m1
  let m = Map.insert index (block,insn) m1
  put (LLState m a b c d e f g h i)
  return (LLReg index)

translateInsn :: LLInsn -> LLMonad LLVal
translateInsn insn = do
  cur <- getCurrent
  let LLCurrentBlock block _ = cur
  translateInsnToBlock block insn

addLocalVar :: String -> LLMonad ()
addLocalVar v = do
  state <- get
  let LLState a b c m1 d e f g h i = state
  let LLCurrentBlock _ vars = c
  let m = if Map.member v m1 then m1 else Map.insert v (Map.lookup v vars) m1
  put (LLState a b c m d e f g h i)
  return ()

getVarsUndo :: LLMonad LLVarsUndo
getVarsUndo = do
  state <- get 
  let LLState _ _ _ m _ _ _ _ _ _= state
  return m

setVarsUndo :: LLVarsUndo -> LLMonad ()
setVarsUndo m = do
  state <- get
  let LLState a b c _ d e f g h i= state
  put (LLState a b c m d e f g h i)
  return ()

setVar :: String -> (LLVal, LLType) -> LLMonad ()
setVar s p = do
  state <- get
  let LLState a b (LLCurrentBlock idx m1) c d e f g h i= state
  case Map.lookup s m1 of
    Just (_, t) -> do
      v <- translateCast t p
      state <- get
      let LLState a b (LLCurrentBlock idx m1) c d e f g h i= state
      let m = Map.insert s (v, t) m1
      put (LLState a b (LLCurrentBlock idx m) c d e f g h i)
      return ()
    Nothing -> do
      st <- getSelfType
      let Just sn = st
      (fm, _, _, _) <- getStructDef sn
      let (idx, t) = fm Map.! s
      v <- translateCast t p
      translateInsn (LLInsnObjectStore sn t LLSelf idx v)
      return ()

declVar :: LLType -> String -> (LLVal, LLType) -> LLMonad ()
declVar t s p = do
  v <- translateCast t p
  addLocalVar s
  state <- get
  let LLState a b (LLCurrentBlock idx m1) c d e f g h i = state
  let m = Map.insert s (v, t) m1
  put (LLState a b (LLCurrentBlock idx m) c d e f g h i)
  return ()

undoVar :: String -> Maybe (LLVal, LLType) -> LLVarMap -> LLVarMap
undoVar var Nothing acc = Map.delete var acc
undoVar var (Just val) acc = Map.insert var val acc

getCurrent :: LLMonad LLCurrent
getCurrent = do
  state <- get
  let LLState _ _ c _ _ _ _ _ _ _= state
  return c

setCurrent :: LLCurrent -> LLMonad ()
setCurrent c = do
  state <- get
  let LLState a b _ d e f g h i j= state
  put(LLState a b c d e f g h i j)
  return ()


startBlock :: Int -> LLMonad Int
startBlock parentIndex = do
  parentBlock <- getBlock parentIndex
  let LLBlock _ parentDepth _ = parentBlock
  let newBlock = LLBlock parentIndex (parentDepth+1) LLOpen
  state <- get
  let LLState a m1 b c d e f g h i = state
  let index = Map.size m1
  let m = Map.insert index newBlock m1
  put (LLState a m b c d e f g h i)
  return index

getBlock :: Int -> LLMonad LLBlock
getBlock index = do
  state <- get 
  let LLState _ m _ _ _ _ _ _ _ _ = state
  return (m Map.! index)

getStructMap :: LLMonad LLStructMap
getStructMap = do
  state <- get
  let LLState _ _ _ _ _ _ _ sm _ _ = state
  return sm

getStructDef :: String -> LLMonad LLStructDef
getStructDef s = do
  sm <- getStructMap
  return (sm Map.! s)

getSelfType :: LLMonad (Maybe String)
getSelfType = do
  state <- get
  let LLState _ _ _ _ _ _ _ _ t _ = state
  return t

getReturnType :: LLMonad LLType
getReturnType = do
  state <- get
  let LLState _ _ _ _ _ _ _ _ _ t = state
  return t

endBlock :: LLEnd -> LLMonad ()
endBlock end = do
  state <- get
  let LLState a m1 (LLCurrentBlock i _) c d e f g h j = state
  let currentBlock = m1 Map.! i
  let LLBlock parent depth _ = currentBlock
  let newBlock = LLBlock parent depth end
  let m = Map.insert i newBlock m1
  put (LLState a m LLCurrentNone c d e f g h j)
  return ()


makePhi :: LLVarMap -> LLVarMap -> String -> (Int, LLVal)
makePhi phiVars srcVars phi = 
  let (LLReg idx, _) = phiVars Map.! phi in (idx, fst (srcVars Map.! phi))

makePhis :: LLVarMap -> (Set String) -> LLVarMap -> (Map Int LLVal)
makePhis phiVars phis srcVars = Map.fromList(map (makePhi phiVars srcVars) (Set.toList phis))

translateLoopPhi :: Int -> LLVarMap -> String -> LLMonad LLVarMap
translateLoopPhi block vars s = do
  let typ = snd $ vars Map.! s
  val <- translateInsnToBlock block (LLInsnPhi typ)
  return (Map.insert s (val, typ) vars)

translateString :: String -> LLMonad LLVal
translateString string = do
  state <- get
  let LLState a b c d e m1 f g h i= state
  case Map.lookup string m1 of
    Nothing -> do
      let idx = Map.size m1
      let bs = encodeUtf8 $ T.pack string
      let l = ByteString.length bs + 1
      let m = Map.insert string (idx, l, bs) m1
      put (LLState a b c d e m f g h i)
      return (LLConstStr idx l)
    Just (idx, l, _) -> return (LLConstStr idx l)

translateWhile :: (Expr Location) -> (Stmt Location) -> (Set String) -> LLMonad()
translateWhile (ELitFalse _) _ _ = return()
translateWhile (ELitTrue loc)  stmt phiVars = do 
  state <- get  
  cur <- getCurrent
  let LLCurrentBlock curBlock curVars = cur
  loopBlock <- startBlock curBlock
  loopVars <- foldM (translateLoopPhi loopBlock) curVars phiVars
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
  loopVars <- foldM (translateLoopPhi loopBlock) curVars phiVars
  let curPhis = makePhis loopVars phiVars curVars
  endBlock $ LLJoin (loopBlock, curPhis)
  setCurrent $ LLCurrentBlock loopBlock loopVars
  okBlock <- startBlock loopBlock
  exitBlock <- startBlock loopBlock
  translateExprAsCond expr (okBlock, Map.empty) (exitBlock, Map.empty)
  setCurrent $ LLCurrentBlock okBlock loopVars
  translateStmt stmt
  after <- getCurrent
  case after of
    LLCurrentNone -> setCurrent $ LLCurrentBlock exitBlock loopVars
    LLCurrentBlock afterBlock afterVars -> do
      let actualPhiVars = Set.fromList $ map (\(a, _, _, _) -> a) (findPhis afterVars curVars)
      if Set.isSubsetOf actualPhiVars phiVars then do
        let afterPhis = makePhis loopVars phiVars afterVars
        endBlock $ LLJoin (loopBlock, afterPhis)
        setCurrent $ LLCurrentBlock exitBlock loopVars
      else do
        put state
        translateWhile expr stmt (Set.union phiVars actualPhiVars)

translateCast :: LLType -> (LLVal, LLType) -> LLMonad LLVal
translateCast t1 (v2, t2) =
  if t1 == t2 then return v2
  else translateSimpleExpr (LLInsnObjectCast t2 t1 v2)

convertArg :: ((LLVal, LLType), LLType) -> LLMonad (LLVal, LLType)
convertArg (p, t) = do
 v <- translateCast t p
 return (v, t)

convertArgs :: [(LLVal, LLType)] -> [LLType] -> LLMonad [(LLVal, LLType)]
convertArgs args types = mapM convertArg (zip args types)

translateStmt :: Stmt Location -> LLMonad ()
translateBlock :: Block Location -> LLMonad ()
translateExpr :: Expr Location -> LLMonad (LLVal, LLType)
translateItem :: LLType -> Item Location -> LLMonad()
translateExprAsCond :: Expr Location -> LLJump -> LLJump -> LLMonad()

translateExprAsCond (Not _ expr) jTrue jFalse = translateExprAsCond expr jFalse jTrue
translateExprAsCond (EAnd _ e1 e2) jTrue jFalse = do
  cur <- getCurrent
  let LLCurrentBlock curBlock curVars = cur

  e2Block <- startBlock curBlock
  translateExprAsCond e1 (e2Block, Map.empty) jFalse
  setCurrent(LLCurrentBlock e2Block curVars)
  translateExprAsCond e2 jTrue jFalse

translateExprAsCond (EOr _ e1 e2) jTrue jFalse = do
  cur <- getCurrent
  let LLCurrentBlock curBlock curVars = cur

  e2Block <- startBlock curBlock
  translateExprAsCond e1 jTrue (e2Block, Map.empty)
  setCurrent(LLCurrentBlock e2Block curVars)
  translateExprAsCond e2 jTrue jFalse

translateExprAsCond expr jTrue jFalse = do
  (v, _) <- translateExpr expr
  endBlock (LLCond v jTrue jFalse)

translateExpr (EVar loc ident) = do
  let Ident s = ident 
  getVar s

translateExpr (ELitInt _ i) = return (LLConstInt i, LLInt)
translateExpr (ELitTrue _) = return (LLConstBool True, LLBool)
translateExpr (ELitFalse _) = return (LLConstBool False, LLBool)
translateExpr (EString _ string) = do 
  val <- translateString (unescape string)
  return (val, LLStr)

translateExpr (Neg _ expr) = do
  (sv, _) <- translateExpr expr
  v <- translateSimpleExpr (LLInsnNeg sv)
  return (v, LLInt)

translateExpr (Not _ expr) = do
  (sv, _) <- translateExpr expr
  v <- translateSimpleExpr (LLInsnNot sv)
  return (v, LLBool)

translateExpr (EMul _ e1 (Times _) e2) = do
  (sv1, _) <- translateExpr e1
  (sv2, _) <- translateExpr e2
  v <- translateSimpleExpr (LLInsnMul sv1 sv2)
  return (v, LLInt)

translateExpr (EMul _ e1 (Div _)  e2) = do
  (sv1, _) <- translateExpr e1
  (sv2, _) <- translateExpr e2
  v <- translateSimpleExpr (LLInsnDiv sv1 sv2)
  return (v, LLInt)

translateExpr (EMul _ e1 (Mod _) e2) = do
  (sv1, _) <- translateExpr e1
  (sv2, _) <- translateExpr e2
  v <- translateSimpleExpr (LLInsnMod sv1 sv2)
  return (v, LLInt)

translateExpr (EAdd _ e1 (Plus _) e2) = do
  (sv1, st1) <- translateExpr e1
  (sv2, _) <- translateExpr e2
  v <- translateSimpleExpr (if st1 == LLInt then (LLInsnAdd sv1 sv2) else (LLInsnCat sv1 sv2))
  return (v, st1)

translateExpr (EAdd _ e1 (Minus _) e2) = do
  (sv1, _) <- translateExpr e1
  (sv2, _) <- translateExpr e2
  v <- translateSimpleExpr (LLInsnSub sv1 sv2)
  return (v, LLInt)

translateExpr (ERel _ e1 (LTH _) e2) = do
  (sv1, _) <- translateExpr e1
  (sv2, _) <- translateExpr e2
  v <- translateSimpleExpr (LLInsnLt sv1 sv2)
  return (v, LLBool)

translateExpr (ERel _ e1 (LE _) e2) = do
  (sv1, _) <- translateExpr e1
  (sv2, _) <- translateExpr e2
  v <- translateSimpleExpr (LLInsnLe sv1 sv2)
  return (v, LLBool)

translateExpr (ERel _ e1 (GTH _) e2) = do
  (sv1, _) <- translateExpr e1
  (sv2, _) <- translateExpr e2
  v <- translateSimpleExpr (LLInsnGt sv1 sv2)
  return (v, LLBool)

translateExpr (ERel _ e1 (GE _) e2) = do
  (sv1, _) <- translateExpr e1
  (sv2, _) <- translateExpr e2
  v <- translateSimpleExpr (LLInsnGe sv1 sv2)
  return (v, LLBool)

translateExpr (ERel _ e1 (EQU _) e2) = do
  (sv1, st) <- translateExpr e1
  (sv2, _) <- translateExpr e2
  v <- translateSimpleExpr (LLInsnEq st sv1 sv2)
  return (v, LLBool)

translateExpr (ERel _ e1 (NE _) e2) = do
  (sv1, st) <- translateExpr e1
  (sv2, _) <- translateExpr e2
  v <- translateSimpleExpr (LLInsnNe st sv1 sv2)
  return (v, LLBool)

translateExpr (EAnd _ e1 e2) = do
  -- what block r we in
  cur <- getCurrent
  let LLCurrentBlock curBlock curVars = cur

  joinBlock <- startBlock curBlock
  fv <- translateInsnToBlock joinBlock (LLInsnPhi LLBool)
  let LLReg phi = fv

  condBlock <- startBlock curBlock
  setCurrent(LLCurrentBlock condBlock curVars)  
  (sv2, _) <- translateExpr e2
  endBlock (LLJoin (joinBlock, (Map.singleton phi sv2)))

  setCurrent cur
  translateExprAsCond e1 (condBlock, Map.empty) (joinBlock, Map.singleton phi (LLConstBool False))

  setCurrent(LLCurrentBlock joinBlock curVars)  
  return (fv, LLBool)

translateExpr (EOr _ e1 e2) = do
  -- what block r we in
  cur <- getCurrent
  let LLCurrentBlock curBlock curVars = cur

  joinBlock <- startBlock curBlock
  setCurrent(LLCurrentBlock joinBlock curVars)  
  fv <- translateInsn (LLInsnPhi LLBool)
  let LLReg phi = fv

  condBlock <- startBlock curBlock
  setCurrent(LLCurrentBlock condBlock curVars)  
  (sv2, _) <- translateExpr e2
  endBlock (LLJoin (joinBlock, (Map.singleton phi sv2)))

  setCurrent cur
  translateExprAsCond e1 (joinBlock, Map.singleton phi (LLConstBool True)) (condBlock, Map.empty)

  setCurrent(LLCurrentBlock joinBlock curVars)  
  return (fv, LLBool)

translateExpr (EApp _ (Ident s) exprs) = do
  args <- mapM translateExpr exprs 
  fd <- getFunc s
  case fd of
    Just (rt, at) -> do
      cargs <- convertArgs args at
      v <- translateInsn (LLInsnCall s cargs rt)
      return (v, rt)
    Nothing -> do
      st <- getSelfType
      let Just sn = st
      (_, mm, _, _) <- getStructDef sn
      let (idx, rt, at, bsn) = mm Map.! s
      cv1 <- translateCast (LLObject bsn) (LLSelf, LLObject sn)
      cargs <- convertArgs args at
      v <- translateInsn (LLInsnObjectCall sn LLSelf idx ((cv1, LLObject bsn):cargs) rt)
      return (v, rt)

translateExpr (ESelf _) = do
  st <- getSelfType
  let Just s = st -- alr checked
  return (LLSelf, LLObject s)

translateExpr (ENull _ (EVar _ (Ident s))) = do
  return (LLNull, LLObject s)

translateExpr (EIndex _ e1 e2) = do
  (v1, t1) <- translateExpr e1
  (v2, _) <- translateExpr e2 -- type is checked
  let LLArray t = t1
  v <- translateInsn (LLInsnArrayLoad t v1 v2)
  return (v, t)

translateExpr (EArr _ t1 e1) = do
  let t = convertType t1
  (v1, _) <- translateExpr e1
  v <- translateInsn (LLInsnArrayNew t v1)
  return (v, LLArray t)

translateExpr (EField _ e1 (Ident s)) = do
  (v1, t1) <- translateExpr e1
  case t1 of
    LLArray t -> do
      v <- translateInsn (LLInsnArrayLength t v1)
      return (v, LLInt)
    LLObject sn -> do
      (fm, _, _, _) <- getStructDef sn
      let (idx, t) = fm Map.! s
      v <- translateInsn (LLInsnObjectLoad sn t v1 idx)
      return (v, t)

translateExpr (EObject _ (Ident s)) = do
  v <- translateInsn (LLInsnObjectNew s)
  -- TODO default vals
  return (v, LLObject s)

translateExpr (EMthdApp _ e1 (Ident s) exprs) = do
  (v1, t1) <- translateExpr e1
  args <- mapM translateExpr exprs
  let LLObject sn = t1
  (_, mm, _, _) <- getStructDef sn
  let (idx, rt, at, bsn) = mm Map.! s
  cv1 <- translateCast (LLObject bsn) (v1, t1)
  cargs <- convertArgs args at
  v <- translateInsn (LLInsnObjectCall sn v1 idx ((cv1, LLObject bsn):cargs) rt)
  return (v, rt)

translateItem t (NoInit _ ident) = do
  let Ident s = ident 
  case t of
    LLInt -> declVar t s (LLConstInt 0, LLInt)
    LLBool -> declVar t s (LLConstBool False, LLBool)
    LLStr -> do
      val <- translateString ""
      declVar t s (val, LLStr)
    LLArray _ -> declVar t s (LLNull, t)
    LLObject _ -> declVar t s (LLNull, t)

translateItem t (Init _ ident expr) = do
  let Ident s = ident
  val <- translateExpr expr
  declVar t s val

translateStmt (VRet _) = do
  endBlock (LLVoidReturn)
translateStmt (Empty _) = return ()
translateStmt (BStmt _ b) = translateBlock b
translateStmt (Decl _ t i) = do
  mapM_ (translateItem $ convertType t) i

translateStmt (Ass _ (EVar _ ident) expr) = do
  let Ident s = ident 
  val <- translateExpr expr 
  setVar s val

translateStmt (Ass _ (EIndex _ e1 e2 ) e3) = do
  (v1, t1) <- translateExpr e1
  (v2, _) <- translateExpr e2
  (v3, t3) <- translateExpr e3
  let LLArray t = t1
  v4 <- translateCast t (v3, t3)
  translateInsn(LLInsnArrayStore t v1 v2 v4)
  return()

translateStmt (Ass _ (EField _ e1 (Ident s)) e2) = do
  (v1, t1) <- translateExpr e1
  (v2, t2) <- translateExpr e2
  let LLObject sn = t1
  (fm, _, _, _) <- getStructDef sn
  let (idx, t) = fm Map.! s
  v3 <- translateCast t (v2, t2)
  translateInsn(LLInsnObjectStore sn t v1 idx v3)
  return()

translateStmt (Incr _ (EVar _ ident)) = do
  let Ident s = ident
  (val, typ) <- getVar s 
  nval <- translateSimpleExpr(LLInsnAdd val (LLConstInt 1))
  setVar s (nval, LLInt)

translateStmt (Incr _ (EIndex _ e1 e2)) = do
  (v1, t1) <- translateExpr e1
  (v2, _) <- translateExpr e2
  let LLArray t = t1
  v3 <- translateInsn(LLInsnArrayLoad t v1 v2)
  nval <- translateSimpleExpr(LLInsnAdd v3 (LLConstInt 1))
  translateInsn(LLInsnArrayStore t v1 v2 nval)
  return()

translateStmt (Incr _ (EField _ e1 (Ident s))) = do
  (v1, t1) <- translateExpr e1
  let LLObject sn = t1
  (fm, _, _, _) <- getStructDef sn
  let (idx, t) = fm Map.! s
  v2 <- translateInsn(LLInsnObjectLoad sn t v1 idx)
  nval <- translateSimpleExpr(LLInsnAdd v2 (LLConstInt 1))
  translateInsn(LLInsnObjectStore sn t v1 idx nval)
  return()

translateStmt (Decr _ (EVar _ ident)) = do
  let Ident s = ident
  (val, typ) <- getVar s 
  nval <- translateSimpleExpr(LLInsnAdd val (LLConstInt (-1)))
  setVar s (nval, LLInt)

translateStmt (Decr _ (EIndex _ e1 e2)) = do
  (v1, t1) <- translateExpr e1
  (v2, _) <- translateExpr e2
  let LLArray t = t1
  v3 <- translateInsn(LLInsnArrayLoad t v1 v2)
  nval <- translateSimpleExpr(LLInsnAdd v3 (LLConstInt (-1)))
  translateInsn(LLInsnArrayStore t v1 v2 nval)
  return()

translateStmt (Decr _ (EField _ e1 (Ident s))) = do
  (v1, t1) <- translateExpr e1
  let LLObject sn = t1
  (fm, _, _, _) <- getStructDef sn
  let (idx, t) = fm Map.! s
  v2 <- translateInsn(LLInsnObjectLoad sn t v1 idx)
  nval <- translateSimpleExpr(LLInsnAdd v2 (LLConstInt (-1)))
  translateInsn(LLInsnObjectStore sn t v1 idx nval)
  return()

translateStmt (SExp _ expr) = do 
  translateExpr expr
  return ()

translateStmt (Cond _ expr stmt) = do
  case expr  of
    ELitTrue _ -> translateStmt stmt
    ELitFalse _ -> return ()
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
          translateExprAsCond expr (condBlock, Map.empty) (joinBlock, Map.empty)
          setCurrent(LLCurrentBlock joinBlock curVars)
        LLCurrentBlock finalCondBlock condVars -> do
          let phis = findPhis condVars curVars
          (joinVars, condPhis, curPhis) <- foldM (emitPhi joinBlock) (curVars, Map.empty, Map.empty) phis
          
          endBlock (LLJoin (joinBlock, condPhis))
          setCurrent cur
          translateExprAsCond expr (condBlock, Map.empty) (joinBlock, curPhis)
          setCurrent(LLCurrentBlock joinBlock joinVars)

translateStmt (CondElse _ expr stmt1 stmt2) = do
  case expr of
    ELitTrue _ -> translateStmt stmt1
    ELitFalse _ -> translateStmt stmt2
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
      translateExprAsCond expr (condBlock1, Map.empty) (condBlock2, Map.empty)
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
  (v1, t1) <- translateExpr expr
  t <- getReturnType
  v <- translateCast t (v1, t1)
  endBlock (LLReturn (v, t))

translateBlockStmt :: Stmt Location -> LLMonad()
translateBlockStmt s = do
  cur <- getCurrent
  if cur == LLCurrentNone then return () else translateStmt s

translateBlock (Block _ stmts) = do
  cur <- getCurrent 
  startVarsUndo <- getVarsUndo
  setVarsUndo Map.empty
  mapM_ translateBlockStmt stmts
  after <- getCurrent
  endVarsUndo <- getVarsUndo
  setVarsUndo startVarsUndo
  case after of
    LLCurrentNone -> return ()
    LLCurrentBlock endBlock endVars -> do
      let finalVars = Map.foldrWithKey undoVar endVars endVarsUndo
      setCurrent $ LLCurrentBlock endBlock finalVars

translateTopBlock :: Block Location -> LLMonad()
translateTopBlock block = do
  translateBlock block
  cur <- getCurrent
  if cur == LLCurrentNone then return () else endBlock LLVoidReturn

getArgType :: Arg Location -> LLType
getArgType (Arg _ t _) = convertType t

convertType :: Type Location -> LLType
convertType (Latte.Int _) = LLInt
convertType (Latte.Str _) = LLStr
convertType (Latte.Bool _) = LLBool
convertType (Latte.Void _) = LLVoid
convertType (Latte.Arr _ t) = LLArray $ convertType t
convertType (Latte.Struct _ (Ident s)) = LLObject s

emitArg :: (Int, Arg Location) -> String
emitArg (i, Arg _ t _) = emitType (convertType t) ++ " %arg" ++ show i

emitType :: LLType -> String
emitType LLInt = "i32"
emitType LLBool = "i1"
emitType LLStr = "i8*"
emitType LLVoid = "void"
emitType (LLArray t) = (emitType t) ++ "*"
emitType (LLObject s) = "%struct." ++ s ++ "*"

emitVal :: LLVal -> String
emitVal (LLReg idx) = "%t" ++ show idx
emitVal (LLConstInt i) = show i
emitVal (LLConstBool False) = "0"
emitVal (LLConstBool True) = "1"
emitVal (LLConstStr idx len) = "getelementptr inbounds ([" ++ show len ++ " x i8], [" ++ show len ++ " x i8]* @.str" ++ show idx ++ ", i64 0, i64 0)"
emitVal (LLArg idx) = "%arg" ++ show idx
emitVal LLSelf = "%self"
emitVal LLNull = "null"

emitCallArg :: (LLVal, LLType) -> String
emitCallArg (v, t) = emitType t ++ " " ++ emitVal v

emitPhiSrc :: (Int, LLVal) -> String
emitPhiSrc (k, v) = "[ " ++ emitVal v ++ ", %block" ++ show k ++ " ]"

emitBlockBiInsn idx op v1 v2 = "    %t" ++ show idx ++ " = " ++ op ++ " " ++ emitVal v1 ++ ", " ++ emitVal v2 ++ "\n"
emitBlockInsn :: Map Int (Map Int LLVal) -> (Int, LLInsn) -> String
emitBlockInsn phiMap (idx, LLInsnAdd v1 v2) = emitBlockBiInsn idx "add i32" v1 v2
emitBlockInsn phiMap (idx, LLInsnSub v1 v2) = emitBlockBiInsn idx "sub i32" v1 v2
emitBlockInsn phiMap (idx, LLInsnMul v1 v2) = emitBlockBiInsn idx "mul i32" v1 v2
emitBlockInsn phiMap (idx, LLInsnDiv v1 v2) = emitBlockBiInsn idx "sdiv i32" v1 v2
emitBlockInsn phiMap (idx, LLInsnMod v1 v2) = emitBlockBiInsn idx "srem i32" v1 v2
emitBlockInsn phiMap (idx, LLInsnEq t v1 v2) = emitBlockBiInsn idx ("icmp eq " ++ emitType t) v1 v2
emitBlockInsn phiMap (idx, LLInsnNe t v1 v2) = emitBlockBiInsn idx ("icmp ne " ++ emitType t) v1 v2
emitBlockInsn phiMap (idx, LLInsnLt v1 v2) = emitBlockBiInsn idx "icmp slt i32" v1 v2
emitBlockInsn phiMap (idx, LLInsnLe v1 v2) = emitBlockBiInsn idx "icmp sle i32" v1 v2
emitBlockInsn phiMap (idx, LLInsnGt v1 v2) = emitBlockBiInsn idx "icmp sgt i32" v1 v2
emitBlockInsn phiMap (idx, LLInsnGe v1 v2) = emitBlockBiInsn idx "icmp sge i32" v1 v2
emitBlockInsn phiMap (idx, LLInsnNeg v1) = emitBlockBiInsn idx "sub i32" (LLConstInt 0) v1
emitBlockInsn phiMap (idx, LLInsnNot v1) = emitBlockBiInsn idx "xor i1" (LLConstBool True) v1
emitBlockInsn phiMap (idx, LLInsnCat v1 v2) = "    %t" ++ show idx ++ " = call i8* @$concat(i8* " ++ emitVal v1 ++ ", i8* " ++ emitVal v2 ++ ")\n"
emitBlockInsn phiMap (idx, LLInsnCall fun args rtyp) = 
  let eArgs = intercalate ", " (map emitCallArg args) in
  case rtyp of
    LLVoid -> "    call void @" ++ fun ++ "(" ++ eArgs ++ ")\n"
    _ -> "    %t" ++ show idx ++ " = call " ++ emitType rtyp ++ " @" ++ fun ++ "(" ++ eArgs ++ ")\n"

emitBlockInsn phiMap (idx, LLInsnArrayLoad t v1 v2) =
  "    %a" ++ show idx ++ " = getelementptr " ++ emitType t ++ ", " ++ emitType t ++ "* " ++ emitVal v1 ++ ", i32 " ++ emitVal v2 ++ "\n    %t" ++ show idx ++ " = load " ++ emitType t ++ ", " ++ emitType t ++ "* %a" ++ show idx ++ "\n"

emitBlockInsn phiMap (idx, LLInsnArrayStore t v1 v2 v3) =
  "    %a" ++ show idx ++ " = getelementptr " ++ emitType t ++ ", " ++ emitType t ++ "* " ++ emitVal v1 ++ ", i32 " ++ emitVal v2 ++ "\n" ++ 
  "    store " ++ emitType t ++" " ++ emitVal v3 ++ ", " ++ emitType t ++ "* %a" ++ show idx ++ "\n"

emitBlockInsn phiMap (idx, LLInsnArrayLength t v) =
  "    %c" ++ show idx ++ " = bitcast " ++ emitType t ++ "* " ++ emitVal v ++ " to i32*\n    %a" ++ show idx ++ " = getelementptr i32, i32* %c" ++ show idx ++ ", i32 -1\n    %t" ++ show idx ++ " = load i32, i32* %a" ++ show idx ++ "\n"

emitBlockInsn phiMap (idx, LLInsnArrayNew LLInt v) =
  "    %t" ++ show idx ++ " = call i32* @$newarrayint(i32 " ++ emitVal v ++ ")\n"

emitBlockInsn phiMap (idx, LLInsnArrayNew LLBool v) =
  "    %t" ++ show idx ++ " = call i1* @$newarraybool(i32 " ++ emitVal v ++ ")\n"

emitBlockInsn phiMap (idx, LLInsnArrayNew LLStr v) =
  "    %t" ++ show idx ++ " = call i8** @$newarraystr(i32 " ++ emitVal v ++ ")\n"

emitBlockInsn phiMap (idx, LLInsnArrayNew t v) =
  "    %a" ++ show idx ++ " = call i8* @$newarrayptr(i32 " ++ emitVal v ++ ")\n" ++
  "    %t" ++ show idx ++ " = bitcast i8* %a" ++ show idx ++ " to " ++ emitType t ++ "*\n"

emitBlockInsn phiMap (idx, LLInsnObjectNew s) = 
  "    %a" ++ show idx ++ " = getelementptr %struct." ++ s ++ ", %struct." ++ s ++ "* null, i32 1\n    %s" ++ show idx ++ " = ptrtoint %struct." ++ s  ++ "* %a" ++ show idx ++ " to i32\n" ++
  "    %v" ++ show idx ++ " = call i8* @$newobject(i32 %s" ++ show idx ++ ")\n" ++
  "    %t" ++ show idx ++ " = bitcast i8* %v" ++ show idx ++ " to %struct." ++ s ++ "* \n" ++
  "    %p" ++ show idx ++ " = getelementptr %struct." ++ s ++ ", %struct." ++ s ++"* %t" ++ show idx ++ ", i32 0, i32 0\n" ++
  "    store %vtable." ++ s ++ "* @vtable." ++ s ++ ", %vtable." ++ s ++ "** %p" ++ show idx ++ "\n"

emitBlockInsn phiMap (idx, LLInsnObjectLoad s t v i) =
  "    %p" ++ show idx ++ " = getelementptr %struct." ++ s ++ ", %struct." ++ s ++"* " ++ emitVal v ++ ", i32 0, i32 " ++ show i ++"\n" ++
  "    %t" ++ show idx ++ " = load " ++ emitType t ++ ", " ++ emitType t ++ "* %p" ++ show idx ++ "\n"

emitBlockInsn phiMap (idx, LLInsnObjectStore s t v1 i v2) =
  "    %p" ++ show idx ++ " = getelementptr %struct." ++ s ++ ", %struct." ++ s ++"* " ++ emitVal v1 ++ ", i32 0, i32 " ++ show i ++"\n" ++
  "    store " ++ emitType t ++" " ++ emitVal v2 ++ ", " ++ emitType t ++ "* %p" ++ show idx ++ "\n"

emitBlockInsn phiMap (idx, LLInsnObjectCall s v1 i args rtyp) = 
  let mt = emitType rtyp ++ "(" ++ intercalate ", " (map (emitType . snd) args) ++ ")" ++ "*" in
  let l0 = "    %a" ++ show idx ++ " = getelementptr %struct." ++ s ++ ", %struct." ++ s ++ "* " ++ emitVal v1 ++ ", i32 0, i32 0\n" in
  let l1 = "    %b" ++ show idx ++ " = load %vtable." ++ s ++ "*, %vtable." ++ s ++ "** %a" ++ show idx ++ "\n" in
  let l2 = "    %c" ++ show idx ++ " = getelementptr %vtable." ++ s ++ ", %vtable." ++ s ++ "* %b" ++ show idx ++ ", i32 0, i32 " ++ show i ++ "\n" in
  let l3 = "    %d" ++ show idx ++ " = load " ++ mt ++ ", " ++ mt ++ "* %c" ++ show idx ++ "\n" in
  let pref = l0 ++ l1 ++ l2 ++ l3 in
  let eArgs = intercalate ", " (map emitCallArg args) in
  case rtyp of
    LLVoid -> pref ++ "    call void %d" ++ show idx ++ "(" ++ eArgs ++ ")\n"
    _ -> pref ++ "    %t" ++ show idx ++ " = call " ++ emitType rtyp ++ " %d" ++ show idx ++ "(" ++ eArgs ++ ")\n"

emitBlockInsn phiMap (idx, LLInsnObjectCast t1 t2 v) =
  "    %t" ++ show idx ++ " = bitcast " ++ emitType t1 ++ " " ++ emitVal v ++ " to " ++ emitType t2 ++ "\n"

emitBlockInsn phiMap (idx, LLInsnPhi typ) =
  let phi = phiMap Map.! idx in
    let srcs = map emitPhiSrc (Map.toList phi) in
    "    %t" ++ show idx ++ " = phi " ++ emitType typ ++ " " ++ intercalate ", " srcs ++ "\n"

emitBlockEnd :: LLEnd -> String
emitBlockEnd LLVoidReturn = "    ret void\n"
emitBlockEnd (LLReturn (v, t)) = "    ret " ++ emitType t ++ " " ++ emitVal v ++ "\n"
emitBlockEnd (LLCond v (b1, _) (b2, _)) = "    br i1 " ++ emitVal v ++ ", label %block" ++ show b1 ++ ", label %block" ++ show b2 ++ "\n"
emitBlockEnd (LLJoin (b, _)) = "    br label %block" ++ show b ++ "\n"

emitBlock :: Map Int [(Int, LLInsn)] -> Map Int (Map Int LLVal) -> (Int, LLBlock) -> String
emitBlock insnsByBlock phiMap (blockIdx, LLBlock _ _ end) =
  let insns = insnsByBlock Map.! blockIdx in
    "  block" ++ show blockIdx ++ ":\n" ++ concat (map (emitBlockInsn phiMap) insns) ++ emitBlockEnd end

sortInsn :: Map Int [(Int, LLInsn)] -> (Int, LLInstruction) -> Map Int [(Int, LLInsn)]
sortInsn m1 (insIdx, (blockIndex, insn))  =
  let tail = m1 Map.! blockIndex in 
    Map.insert blockIndex ((insIdx, insn):tail) m1

sortPhi :: Int -> LLBlock -> Map Int (Map Int LLVal) -> Map Int (Map Int LLVal)
sortPhi blockIdx (LLBlock _ _ end) m1 = case end of
  LLVoidReturn -> m1
  LLReturn _ -> m1
  LLCond _ j1 j2 -> sortPhiJump (sortPhiJump m1 j1 blockIdx) j2 blockIdx
  LLJoin j -> sortPhiJump m1 j blockIdx

sortPhiJump :: Map Int (Map Int LLVal) -> LLJump -> Int -> Map Int (Map Int LLVal)

sortPhiJump m (_, mj)  blockIdx = Map.foldrWithKey (sortPhiJumpVal blockIdx) m mj
sortPhiJumpVal :: Int -> Int -> LLVal -> Map Int (Map Int LLVal) -> Map Int (Map Int LLVal)
sortPhiJumpVal blockIdx phiIdx val m1 = 
  let m2 = Map.findWithDefault Map.empty phiIdx m1 in 
  Map.insert phiIdx (Map.insert blockIdx val m2) m1

emitFun :: LLType -> String -> [Arg Location] -> Map Int LLInstruction -> Map Int LLBlock -> String
emitFun t s args insns blocks = 
  let eArgs = intercalate ", " (map emitArg (zip [0..] args)) in
    let insnByBlock = foldl sortInsn (Map.map (const []) blocks) (Map.toDescList insns) in 
      let phiMap = Map.foldrWithKey sortPhi Map.empty blocks in
        let eBlocks = concat (map (emitBlock insnByBlock phiMap) (Map.toAscList blocks)) in
          "define " ++ emitType t ++ " @" ++ s ++ "(" ++ eArgs ++ ") {\n" ++ eBlocks ++ "}\n\n" 

emitMthd :: String -> LLType -> String -> [Arg Location] -> Map Int LLInstruction -> Map Int LLBlock -> String
emitMthd sn t s args insns blocks = 
  let eArgs = map emitArg (zip [0..] args) in
    let insnByBlock = foldl sortInsn (Map.map (const []) blocks) (Map.toDescList insns) in 
      let phiMap = Map.foldrWithKey sortPhi Map.empty blocks in
        let eBlocks = concat (map (emitBlock insnByBlock phiMap) (Map.toAscList blocks)) in
          "define " ++ emitType t ++ " @" ++ sn ++ "." ++ s ++ "(" ++ intercalate ", " (["%struct." ++ sn ++ "* %self"]  ++ eArgs) ++ ") {\n" ++ eBlocks ++ "}\n\n" 

argToVar :: (Int,Arg Location) -> (String, (LLVal, LLType))
argToVar (index, Arg _ t (Ident s)) = (s, (LLArg index, convertType t))

emitTopDef1 :: TopDef Location -> TopMonad String
emitTopDef1 (FnDef _ t (Ident s)  args block) = return ""

emitTopDef1 (ClassDef _ (Ident s) items) = do
  state <- get
  let TopState _ sm _ = state
  let sd = sm Map.! s
  let (_, _, fieldsMap, methodsMap) = sd
  let fields = Map.toAscList fieldsMap
  let methods = Map.toAscList methodsMap
  let deft = "%struct." ++ s ++ " = type {" ++ intercalate ", " (["%vtable." ++ s ++ "*"] ++ map (emitType . snd) fields) ++ "}\n"
  let defvt = "%vtable." ++ s ++ " = type {" ++ intercalate ", " (map (emitMthdType . snd) methods) ++ "}\n"
  let defv = "@vtable." ++ s ++ " = private constant %vtable." ++ s ++ " {" ++ intercalate ", " (map (emitVtableElement . snd) methods) ++ "}\n"
  return (deft ++ defvt ++ defv)

emitTopDef1 (ClassEDef _ (Ident s) (Ident base) items) = do
  state <- get
  let TopState _ sm _ = state
  let sd = sm Map.! s
  let (_, _, fieldsMap, methodsMap) = sd
  let fields = Map.toAscList fieldsMap
  let methods = Map.toAscList methodsMap
  let deft = "%struct." ++ s ++ " = type {" ++ intercalate ", " (["%vtable." ++ s ++ "*"] ++ map (emitType . snd) fields) ++ "}\n"
  let defvt = "%vtable." ++ s ++ " = type {" ++ intercalate ", " (map (emitMthdType . snd) methods) ++ "}\n"
  let defv = "@vtable." ++ s ++ " = private constant %vtable." ++ s ++ " {" ++ intercalate ", " (map (emitVtableElement . snd) methods) ++ "}\n"
  return (deft ++ defvt ++ defv)

emitTopDef2 :: TopDef Location -> TopMonad String
emitTopDef2 (FnDef _ t (Ident s)  args block) = do
  TopState funs structDefs strings <- get
  let initBlock = LLBlock 0 0 LLOpen
  let initVars = Map.fromList (map argToVar (zip [0..] args))
  let initState = LLState Map.empty (Map.singleton 0 initBlock) (LLCurrentBlock 0 initVars) Map.empty funs strings Map.empty structDefs Nothing (convertType t)
  let (_, LLState insns blocks _ _ _ strings2 _ _ _ _) = runState (translateTopBlock block) initState
  put (TopState funs structDefs strings2)
  return $ emitFun (convertType t) s args insns blocks

emitTopDef2 (ClassDef _ (Ident s) items) = do
  defm <- mapM (emitClassItem s) items
  return (concat defm)

emitTopDef2 (ClassEDef _ (Ident s) (Ident base) items) = do
  defm <- mapM (emitClassItem s) items
  return (concat defm)

emitClassItem :: String -> ClassItem Location -> TopMonad String
emitClassItem _ (FieldDef _ _ _ ) = return ""
emitClassItem sn (MethodDef _ t (Ident s)  args block) = do
  TopState funs structDefs strings <- get
  let initBlock = LLBlock 0 0 LLOpen
  let initVars = Map.fromList (map argToVar (zip [0..] args))
  let initState = LLState Map.empty (Map.singleton 0 initBlock) (LLCurrentBlock 0 initVars) Map.empty funs strings Map.empty structDefs (Just sn) (convertType t)
  let (_, LLState insns blocks _ _ _ strings2 _ _ _ _) = runState (translateTopBlock block) initState
  put (TopState funs structDefs strings2)
  return $ emitMthd sn (convertType t) s args insns blocks

emitMthdType :: (LLType, [LLType], String, String) -> String
emitMthdType (rt, argt, sn, mn) = emitType rt ++ "(" ++ intercalate ", " (["%struct." ++ sn ++ "*"] ++ (map emitType argt)) ++ ")*"
emitVtableElement :: (LLType, [LLType], String, String) -> String
emitVtableElement (rt, argt, sn, mn) = emitMthdType (rt, argt, sn, mn) ++ " @" ++ sn ++ "." ++ mn

emitGlobalStr :: (String, (Int, Int, ByteString)) -> String
emitGlobalStr (_, (idx, len, bs)) = "@.str" ++ show idx ++ " = private constant [" ++ show len ++ " x i8] c\"" ++ concat (map (printf "\\%02X") (ByteString.unpack bs)) ++ "\\00\"\n"

llHeader = (
  "declare i8* @$concat(i8*, i8*)\n" ++
  "declare i8* @$newobject(i32)\n" ++
  "declare i32* @$newarrayint(i32)\n" ++
  "declare i1* @$newarraybool(i32)\n" ++
  "declare i8** @$newarraystr(i32)\n" ++
  "declare i8* @$newarrayptr(i32)\n" ++
  "declare void @printInt(i32)\n" ++
  "declare void @printString(i8*)\n" ++
  "declare void @error()\n" ++
  "declare i32 @readInt()\n" ++
  "declare i8* @readString()\n")

emitProgram :: Program Location -> TopMonad String
emitProgram (Program _ topDefs) = do
  tops1 <- mapM emitTopDef1 topDefs 
  tops2 <- mapM emitTopDef2 topDefs 
  TopState _ _ strings <- get
  let strs = map emitGlobalStr (Map.toList strings)
  return $ llHeader ++ concat (tops1 ++ tops2 ++ strs)

builtinFnTypes :: [(String, (LLType, [LLType]))]
builtinFnTypes = [
    ("printInt", (LLVoid, [LLInt])),
    ("printString", (LLVoid, [LLStr])),
    ("error", (LLVoid, [])),
    ("readInt", (LLInt, [])),
    ("readString", (LLStr, []))]

getFnType :: TopDef Location -> [(String, (LLType, [LLType]))]
getFnType (FnDef _ t ident arg block) =
  let Ident s = ident in [(s, (convertType t, map getArgType arg))]
getFnType _ = []

getFnTypes :: Program Location -> LLFuncMap
getFnTypes (Program _ topDefs) = Map.fromList(builtinFnTypes ++ concat (map getFnType topDefs))

makeStructItem :: String -> LLStructDef -> ClassItem Location -> LLStructDef
makeStructItem sn (a, b, c, d) (FieldDef _ t (Ident s)) =
  let idx = (Map.size c) + 1 in
  let tt = convertType t in
  (Map.insert s (idx, tt) a, b, Map.insert idx tt c, d)

makeStructItem sn (a, b, c, d) (MethodDef _ t (Ident s) args stmt) =
  case Map.lookup s b of
    Nothing ->
      let idx = Map.size d in
      let tt = convertType t in
      let argt = map getArgType args in
      (a, Map.insert s (idx, tt, argt, sn) b, c, Map.insert idx (tt, argt, sn, s) d)
    Just (idx, tt, argt, _) ->
      (a, Map.insert s (idx, tt, argt, sn) b, c, Map.insert idx (tt, argt, sn, s) d)

makeStructDef :: LLStructMap -> TopDef Location -> LLStructMap
makeStructDef m (ClassDef _ (Ident s) items) =
  let basemap = (Map.empty, Map.empty, Map.empty, Map.empty) in
  let sd = foldl (makeStructItem s) basemap items in
  Map.insert s sd m
makeStructDef m (ClassEDef _ (Ident s) (Ident base) items) = 
  let basemap = m Map.! base in
  let sd = foldl (makeStructItem s) basemap items in
  Map.insert s sd m
makeStructDef m _ = m

makeStructDefs :: Program Location -> LLStructMap
makeStructDefs (Program _ topDefs) = foldl makeStructDef Map.empty topDefs

allToLLVM :: Program Location -> String
allToLLVM prog = 
  let structDefs = makeStructDefs prog in
    let fnTypes = getFnTypes prog in
      let initState = TopState fnTypes structDefs Map.empty in
        fst $ runState (emitProgram prog) initState 

ico :: T.Text
ico = T.pack(".lat")
baseName :: String -> String
baseName f = T.unpack(Data.Maybe.fromJust(T.stripSuffix ico (T.pack f)))

main :: IO ()
main = do
  args <- getArgs
  text <- readFile $ head $ args
  let base = baseName $ head $ args
  let llFile = base ++ ".ll"
  let bcFile = base ++ ".bc"
  case pProgram $ myLexer $ text of
        Bad s -> die ("ERROR\n" ++ s)
        Ok tree -> do
            case checkTypes tree of
                Right () -> do
                    hPutStrLn stderr "OK"
                    writeFile llFile (allToLLVM tree)
                    callProcess "llvm-link" [llFile, "lib/runtime.bc", "-o", bcFile]
                Left s -> die ("ERROR\n" ++ s)

