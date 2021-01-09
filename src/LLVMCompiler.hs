
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
data LLState = LLState (Map Int LLInstruction) (Map Int LLBlock) LLCurrent LLVarsUndo LLFuncMap LLStringMap
type LLVarsUndo = Map String (Maybe (LLVal, LLType))
type LLFuncMap = Map String (LLType, [LLType])
type LLStringMap = Map String (Int, Int, ByteString)
type LLVarMap = Map String (LLVal, LLType)
type LLInstruction = (Int, LLInsn)
data LLInsn = 	LLInsnAdd LLVal LLVal | 
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
		LLInsnPhi LLType 
data LLType = LLInt | LLStr | LLBool | LLVoid deriving (Eq, Show)
data LLVal = LLReg Int | LLConstInt Integer | LLConstBool Bool | LLConstStr Int Int | LLArg Int deriving Eq
-- params are: parent index and depth and end
data LLBlock = LLBlock Int Int LLEnd 
type LLJump = (Int, Map Int LLVal)
data LLEnd = LLVoidReturn | LLReturn (LLVal, LLType) | LLCond LLVal LLJump LLJump | LLJoin LLJump | LLOpen
data LLCurrent = LLCurrentBlock Int LLVarMap | LLCurrentNone deriving Eq
type LLMonad a = State LLState a

data TopState = TopState LLFuncMap LLStringMap
type TopMonad a = State TopState a

translateProgram :: Program Location -> TopMonad String
translateTopDef :: TopDef Location-> TopMonad String

unescape_tail :: String -> String
unescape_tail "\"" = ""
unescape_tail ('\\':'\\':t) = '\\':(unescape_tail t)
unescape_tail ('\\':'"':t) = '\"':(unescape_tail t)
unescape_tail ('\\':'t':t) = '\t':(unescape_tail t)
unescape_tail ('\\':'r':t) = '\r':(unescape_tail t)
unescape_tail ('\\':'n':t) = '\n':(unescape_tail t)
unescape_tail ('\\':'f':t) = '\f':(unescape_tail t)
unescape_tail ('\\':_:t) = undefined
unescape_tail (h:t) = h:(unescape_tail t)

unescape :: String -> String
unescape ('\"':t) = unescape_tail t


findPhis_ [] m2 = []
findPhis_ ((k,(v,t)):tail) m2 = 
  let (v2, _) = (m2 Map.! k) in 
  if v==v2 then findPhis_ tail m2 else (k, t, v, v2):(findPhis_ tail m2)

findPhis :: LLVarMap -> LLVarMap -> [(String, LLType, LLVal, LLVal)]
findPhis m1 m2 = findPhis_ (Map.toList m1) m2

-- 
emitPhi :: Int -> (LLVarMap, Map Int LLVal, Map Int LLVal) -> (String, LLType, LLVal, LLVal) -> LLMonad (LLVarMap, Map Int LLVal, Map Int LLVal)

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
  cur <- getCurrent
  let LLCurrentBlock block _ = cur
  emitInsnToBlock block insn

addLocalVar :: String -> LLMonad ()
addLocalVar v = do
  state <- get
  let LLState a b c m1 d e = state
  let LLCurrentBlock _ vars = c
  let m = if Map.member v m1 then m1 else Map.insert v (Map.lookup v vars) m1
  put (LLState a b c m d e)
  return ()

getVarsUndo :: LLMonad LLVarsUndo
getVarsUndo = do
  state <- get 
  let LLState _ _ _ m _ _= state
  return m

setVarsUndo :: LLVarsUndo -> LLMonad ()
setVarsUndo m = do
  state <- get
  let LLState a b c _ d e = state
  put (LLState a b c m d e)
  return ()

setVar :: String -> (LLVal, LLType) -> LLMonad ()
setVar s v = do
  state <- get
  let LLState a b (LLCurrentBlock i m1) c d e = state
  let m = Map.insert s v m1
  put (LLState a b (LLCurrentBlock i m) c d e)
  return ()

undoVar :: String -> Maybe (LLVal, LLType) -> LLVarMap -> LLVarMap
undoVar var Nothing acc = Map.delete var acc
undoVar var (Just val) acc = Map.insert var val acc

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


makePhi :: LLVarMap -> LLVarMap -> String -> (Int, LLVal)

makePhi phiVars srcVars phi = 
  let (LLReg idx, _) = phiVars Map.! phi in (idx, fst (srcVars Map.! phi))

makePhis :: LLVarMap -> (Set String) -> LLVarMap -> (Map Int LLVal)
makePhis phiVars phis srcVars = Map.fromList(map (makePhi phiVars srcVars) (Set.toList phis))

emitLoopPhi :: Int -> LLVarMap -> String -> LLMonad LLVarMap
emitLoopPhi block vars s = do
  let typ = snd $ vars Map.! s
  val <- emitInsnToBlock block (LLInsnPhi typ)
  return (Map.insert s (val, typ) vars)

emitString :: String -> LLMonad LLVal
emitString string = do
  state <- get
  let LLState a b c d e m1 = state
  case Map.lookup string m1 of
    Nothing -> do
      let idx = Map.size m1
      let bs = encodeUtf8 $ T.pack string
      let l = ByteString.length bs + 1
      let m = Map.insert string (idx, l, bs) m1
      put (LLState a b c d e m)
      return (LLConstStr idx l)
    Just (idx, l, _) -> return (LLConstStr idx l)

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
  postCond <- getCurrent
  let LLCurrentBlock postCondBlock postCondVars = postCond
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
translateItem :: LLType -> Item Location -> LLMonad()

translateExpr (EVar loc ident) = do
  let Ident s = ident 
  getVar s

translateExpr (ELitInt _ i) = return (LLConstInt i, LLInt)
translateExpr (ELitTrue _) = return (LLConstBool True, LLBool)
translateExpr (ELitFalse _) = return (LLConstBool False, LLBool)
translateExpr (EString _ string) = do 
  val <- emitString (unescape string)
  return (val, LLStr)

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
  (sv1, st) <- translateExpr e1
  (sv2, _) <- translateExpr e2
  v <- emitSimpleExpr (LLInsnEq st sv1 sv2)
  return (v, LLBool)

translateExpr (ERel _ e1 (NE _) e2) = do
  (sv1, st) <- translateExpr e1
  (sv2, _) <- translateExpr e2
  v <- emitSimpleExpr (LLInsnNe st sv1 sv2)
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
  mapM_ (translateItem $ convertType t) i

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

translateItem t (NoInit _ ident) = do
  let Ident s = ident 
  addLocalVar s
  case t of
    LLInt -> setVar s (LLConstInt 0, LLInt)
    LLBool -> setVar s (LLConstBool False, LLBool)
    LLStr -> do
      val <- emitString "" 
      setVar s (val, LLStr) 

translateItem _ (Init _ ident expr) = do
  let Ident s = ident
  val <- translateExpr expr
  addLocalVar s 
  setVar s val

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

getArgType :: Arg Location -> LLType
getArgType (Arg _ t _) = convertType t


convertType :: Type Location -> LLType
convertType (Latte.Int _) = LLInt
convertType (Latte.Str _) = LLStr
convertType (Latte.Bool _) = LLBool
convertType (Latte.Void _) = LLVoid


builtinFnTypes :: [(String, (LLType, [LLType]))]
builtinFnTypes = [
	("printInt", (LLVoid, [LLInt])),
	("printString", (LLVoid, [LLStr])),
	("error", (LLVoid, [])),
	("readInt", (LLInt, [])),
	("readString", (LLStr, []))]

getFnTypes :: Program Location -> LLFuncMap
getFnTypes (Program _ topDefs) = Map.fromList(builtinFnTypes ++ map getFnType topDefs)

getFnType :: TopDef Location -> (String, (LLType, [LLType]))

getFnType (FnDef _ t ident arg block) =
  let Ident s = ident in (s, (convertType t, map getArgType arg))


emitGlobalStr :: (String, (Int, Int, ByteString)) -> String
emitGlobalStr (_, (idx, len, bs)) = "@.str" ++ show idx ++ " = private constant [" ++ show len ++ " x i8] c\"" ++ concat (map (printf "\\%02X") (ByteString.unpack bs)) ++ "\\00\"\n"

allToLLVM :: Program Location -> String
allToLLVM prog = 
  let fnTypes = getFnTypes prog in 
    let initState = TopState fnTypes Map.empty in
      fst $ runState (translateProgram prog) initState 

llheader = (
  "declare i8* @$concat(i8*, i8*)\n" ++
  "declare void @printInt(i32)\n" ++
  "declare void @printString(i8*)\n" ++
  "declare void @error()\n" ++
  "declare i32 @readInt()\n" ++
  "declare i8* @readString()\n")

translateProgram (Program _ topDefs) = do
  tops <- mapM translateTopDef topDefs 
  TopState _ strings <- get
  let strs = map emitGlobalStr (Map.toList strings)
  return $ llheader ++ concat (tops ++ strs)

argToVar :: (Int,Arg Location) -> (String, (LLVal, LLType))
argToVar (index, Arg _ t (Ident s)) = (s, (LLArg index, convertType t))

-- lol. 
translateTopBlock :: Block Location -> LLMonad()
translateTopBlock block = do
  translateBlock block
  cur <- getCurrent 
  if cur == LLCurrentNone then return () else endBlock LLVoidReturn 

translateTopDef (FnDef _ t (Ident s)  args block) = do
  TopState funs strings <- get
  let initBlock = LLBlock 0 0 LLOpen
  let initVars = Map.fromList (map argToVar (zip [0..] args))
  let initState = LLState Map.empty (Map.singleton 0 initBlock) (LLCurrentBlock 0 initVars) Map.empty funs strings
  let (_, LLState insns blocks _ _ _ strings2) = runState (translateTopBlock block) initState
  put (TopState funs strings2)
  return $ emitFun (convertType t) s args insns blocks

emitBlockInsn :: Map Int (Map Int LLVal) -> (Int, LLInsn) -> String
emitBlockInsn phiMap (idx, LLInsnAdd v1 v2) = emitBlockBiInsn idx "add i32" v1 v2
emitBlockInsn phiMap (idx, LLInsnSub v1 v2) = emitBlockBiInsn idx "sub i32" v1 v2
emitBlockInsn phiMap (idx, LLInsnMul v1 v2) = emitBlockBiInsn idx "mul i32" v1 v2
emitBlockInsn phiMap (idx, LLInsnDiv v1 v2) = emitBlockBiInsn idx "sdiv i32" v1 v2
emitBlockInsn phiMap (idx, LLInsnMod v1 v2) = emitBlockBiInsn idx "srem i32" v1 v2
emitBlockInsn phiMap (idx, LLInsnEq LLInt v1 v2) = emitBlockBiInsn idx "icmp eq i32" v1 v2
emitBlockInsn phiMap (idx, LLInsnNe LLInt v1 v2) = emitBlockBiInsn idx "icmp ne i32" v1 v2
emitBlockInsn phiMap (idx, LLInsnEq LLBool v1 v2) = emitBlockBiInsn idx "icmp eq i1" v1 v2
emitBlockInsn phiMap (idx, LLInsnNe LLBool v1 v2) = emitBlockBiInsn idx "icmp ne i1" v1 v2
emitBlockInsn phiMap (idx, LLInsnLt v1 v2) = emitBlockBiInsn idx "icmp slt i32" v1 v2
emitBlockInsn phiMap (idx, LLInsnLe v1 v2) = emitBlockBiInsn idx "icmp sle i32" v1 v2
emitBlockInsn phiMap (idx, LLInsnGt v1 v2) = emitBlockBiInsn idx "icmp sgt i32" v1 v2
emitBlockInsn phiMap (idx, LLInsnGe v1 v2) = emitBlockBiInsn idx "icmp sge i32" v1 v2
emitBlockInsn phiMap (idx, LLInsnNeg v1) = emitBlockBiInsn idx "sub i32" (LLConstInt 0) v1
emitBlockInsn phiMap (idx, LLInsnNot v1) = emitBlockBiInsn idx "xor i1" (LLConstBool True) v1
emitBlockInsn phiMap (idx, LLInsnCat v1 v2) = "    %t" ++ show idx ++ " = call i8* @$concat(i8* " ++ emitVal v1 ++ ", i8* " ++ emitVal v2 ++ ")\n"
-- LInsnCall String [(LLVal, LLType)] LLType |
emitBlockInsn phiMap (idx, LLInsnCall fun args rtyp) = 
  let eArgs = intercalate ", " (map emitCallArg args) in
  case rtyp of
    LLVoid -> "    call void @" ++ fun ++ "(" ++ eArgs ++ ")\n"
    _ -> "    %t" ++ show idx ++ " = call " ++ emitType rtyp ++ " @" ++ fun ++ "(" ++ eArgs ++ ")\n"
emitBlockInsn phiMap (idx, LLInsnPhi typ) = 
  let phi = phiMap Map.! idx in
    let srcs = map emitPhiSrc (Map.toList phi) in
    "    %t" ++ show idx ++ " = phi " ++ emitType typ ++ " " ++ intercalate ", " srcs ++ "\n"

emitCallArg :: (LLVal, LLType) -> String
emitCallArg (v, t) = emitType t ++ " " ++ emitVal v

emitPhiSrc :: (Int, LLVal) -> String
emitPhiSrc (k, v) = "[ " ++ emitVal v ++ ", %block" ++ show k ++ " ]"

emitBlockBiInsn idx op v1 v2 = "    %t" ++ show idx ++ " = " ++ op ++ " " ++ emitVal v1 ++ ", " ++ emitVal v2 ++ "\n"

emitBlockEnd :: LLEnd -> String
emitBlockEnd LLVoidReturn = "    ret void\n"
emitBlockEnd (LLReturn (v, t)) = "    ret " ++ emitType t ++ " " ++ emitVal v ++ "\n"
emitBlockEnd (LLCond v (b1, _) (b2, _)) = "    br i1 " ++ emitVal v ++ ", label %block" ++ show b1 ++ ", label %block" ++ show b2 ++ "\n"
emitBlockEnd (LLJoin (b, _)) = "    br label %block" ++ show b ++ "\n"

emitVal :: LLVal -> String
emitVal (LLReg idx) = "%t" ++ show idx
emitVal (LLConstInt i) = show i
emitVal (LLConstBool False) = "0"
emitVal (LLConstBool True) = "1"
emitVal (LLConstStr idx len) = "getelementptr inbounds ([" ++ show len ++ " x i8], [" ++ show len ++ " x i8]* @.str" ++ show idx ++ ", i64 0, i64 0)"
emitVal (LLArg idx) = "%arg" ++ show idx

emitBlock :: Map Int [(Int, LLInsn)] -> Map Int (Map Int LLVal) -> (Int, LLBlock) -> String
emitBlock insnsByBlock phiMap (blockIdx, LLBlock _ _ end) =
  let insns = insnsByBlock Map.! blockIdx in
    "  block" ++ show blockIdx ++ ":\n" ++ concat (map (emitBlockInsn phiMap) insns) ++ emitBlockEnd end

emitFun :: LLType -> String -> [Arg Location] -> Map Int LLInstruction -> Map Int LLBlock -> String
emitFun t s args insns blocks = 
  let eArgs = intercalate ", " (map emitArg (zip [0..] args)) in
    let insnByBlock = foldl sortInsn (Map.map (const []) blocks) (Map.toDescList insns) in 
      let phiMap = Map.foldrWithKey sortPhi Map.empty blocks in
        let eBlocks = concat (map (emitBlock insnByBlock phiMap) (Map.toAscList blocks)) in
          "define " ++ emitType t ++ " @" ++ s ++ "(" ++ eArgs ++ ") {\n" ++ eBlocks ++ "}\n\n" 


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

emitArg :: (Int, Arg Location) -> String
emitArg (i, Arg _ t _) = emitType (convertType t) ++ " %arg" ++ show i

emitType :: LLType -> String
emitType LLInt = "i32"
emitType LLBool = "i1"
emitType LLStr = "i8*"
emitType LLVoid = "void"

ico :: T.Text
ico = T.pack(".lat")
outputName :: String -> String
outputName f = T.unpack(Data.Maybe.fromJust(T.stripSuffix ico (T.pack f))) ++ ".ll"

main :: IO ()
main = do
  args <- getArgs
  text <- readFile $ head $ args
  case pProgram $ myLexer $ text of
        Bad s -> die ("ERROR\n" ++ s)
        Ok tree -> do
            case checkTypes tree of
                Right () -> do
			hPutStrLn stderr "OK"
			writeFile (outputName $ head $ args) (allToLLVM tree)
			callProcess "llvm-as" [outputName $ head $ args]
                Left s -> die ("ERROR\n" ++ s)

