{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

-- | Pretty-printer for PrintLatte.
--   Generated by the BNF converter.

module PrintLatte where

import qualified AbsLatte
import Data.Char

-- | The top-level printing method.

printTree :: Print a => a -> String
printTree = render . prt 0

type Doc = [ShowS] -> [ShowS]

doc :: ShowS -> Doc
doc = (:)

render :: Doc -> String
render d = rend 0 (map ($ "") $ d []) "" where
  rend i ss = case ss of
    "["      :ts -> showChar '[' . rend i ts
    "("      :ts -> showChar '(' . rend i ts
    "{"      :ts -> showChar '{' . new (i+1) . rend (i+1) ts
    "}" : ";":ts -> new (i-1) . space "}" . showChar ';' . new (i-1) . rend (i-1) ts
    "}"      :ts -> new (i-1) . showChar '}' . new (i-1) . rend (i-1) ts
    [";"]        -> showChar ';'
    ";"      :ts -> showChar ';' . new i . rend i ts
    t  : ts@(p:_) | closingOrPunctuation p -> showString t . rend i ts
    t        :ts -> space t . rend i ts
    _            -> id
  new i     = showChar '\n' . replicateS (2*i) (showChar ' ') . dropWhile isSpace
  space t s =
    case (all isSpace t', null spc, null rest) of
      (True , _   , True ) -> []              -- remove trailing space
      (False, _   , True ) -> t'              -- remove trailing space
      (False, True, False) -> t' ++ ' ' : s   -- add space if none
      _                    -> t' ++ s
    where
      t'          = showString t []
      (spc, rest) = span isSpace s

  closingOrPunctuation :: String -> Bool
  closingOrPunctuation [c] = c `elem` closerOrPunct
  closingOrPunctuation _   = False

  closerOrPunct :: String
  closerOrPunct = ")],;"

parenth :: Doc -> Doc
parenth ss = doc (showChar '(') . ss . doc (showChar ')')

concatS :: [ShowS] -> ShowS
concatS = foldr (.) id

concatD :: [Doc] -> Doc
concatD = foldr (.) id

replicateS :: Int -> ShowS -> ShowS
replicateS n f = concatS (replicate n f)

-- | The printer class does the job.

class Print a where
  prt :: Int -> a -> Doc
  prtList :: Int -> [a] -> Doc
  prtList i = concatD . map (prt i)

instance {-# OVERLAPPABLE #-} Print a => Print [a] where
  prt = prtList

instance Print Char where
  prt _ s = doc (showChar '\'' . mkEsc '\'' s . showChar '\'')
  prtList _ s = doc (showChar '"' . concatS (map (mkEsc '"') s) . showChar '"')

mkEsc :: Char -> Char -> ShowS
mkEsc q s = case s of
  _ | s == q -> showChar '\\' . showChar s
  '\\'-> showString "\\\\"
  '\n' -> showString "\\n"
  '\t' -> showString "\\t"
  _ -> showChar s

prPrec :: Int -> Int -> Doc -> Doc
prPrec i j = if j < i then parenth else id

instance Print Integer where
  prt _ x = doc (shows x)

instance Print Double where
  prt _ x = doc (shows x)

instance Print AbsLatte.Ident where
  prt _ (AbsLatte.Ident i) = doc $ showString $ i

instance Print (AbsLatte.Program a) where
  prt i e = case e of
    AbsLatte.Program _ topdefs -> prPrec i 0 (concatD [prt 0 topdefs])

instance Print (AbsLatte.TopDef a) where
  prt i e = case e of
    AbsLatte.FnDef _ type_ id args block -> prPrec i 0 (concatD [prt 0 type_, prt 0 id, doc (showString "("), prt 0 args, doc (showString ")"), prt 0 block])
    AbsLatte.ClassDef _ id classitems -> prPrec i 0 (concatD [doc (showString "class"), prt 0 id, doc (showString "{"), prt 0 classitems, doc (showString "}")])
    AbsLatte.ClassEDef _ id1 id2 classitems -> prPrec i 0 (concatD [doc (showString "class"), prt 0 id1, doc (showString "extends"), prt 0 id2, doc (showString "{"), prt 0 classitems, doc (showString "}")])
  prtList _ [x] = concatD [prt 0 x]
  prtList _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print (AbsLatte.ClassItem a) where
  prt i e = case e of
    AbsLatte.FieldDef _ type_ id -> prPrec i 0 (concatD [prt 0 type_, prt 0 id, doc (showString ";")])
    AbsLatte.MethodDef _ type_ id args block -> prPrec i 0 (concatD [prt 0 type_, prt 0 id, doc (showString "("), prt 0 args, doc (showString ")"), prt 0 block])
  prtList _ [x] = concatD [prt 0 x]
  prtList _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print [AbsLatte.TopDef a] where
  prt = prtList

instance Print [AbsLatte.ClassItem a] where
  prt = prtList

instance Print (AbsLatte.Arg a) where
  prt i e = case e of
    AbsLatte.Arg _ type_ id -> prPrec i 0 (concatD [prt 0 type_, prt 0 id])
  prtList _ [] = concatD []
  prtList _ [x] = concatD [prt 0 x]
  prtList _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print [AbsLatte.Arg a] where
  prt = prtList

instance Print (AbsLatte.Block a) where
  prt i e = case e of
    AbsLatte.Block _ stmts -> prPrec i 0 (concatD [doc (showString "{"), prt 0 stmts, doc (showString "}")])

instance Print [AbsLatte.Stmt a] where
  prt = prtList

instance Print (AbsLatte.Stmt a) where
  prt i e = case e of
    AbsLatte.Empty _ -> prPrec i 0 (concatD [doc (showString ";")])
    AbsLatte.BStmt _ block -> prPrec i 0 (concatD [prt 0 block])
    AbsLatte.Decl _ type_ items -> prPrec i 0 (concatD [prt 0 type_, prt 0 items, doc (showString ";")])
    AbsLatte.Ass _ expr1 expr2 -> prPrec i 0 (concatD [prt 0 expr1, doc (showString "="), prt 0 expr2, doc (showString ";")])
    AbsLatte.Incr _ expr -> prPrec i 0 (concatD [prt 0 expr, doc (showString "++"), doc (showString ";")])
    AbsLatte.Decr _ expr -> prPrec i 0 (concatD [prt 0 expr, doc (showString "--"), doc (showString ";")])
    AbsLatte.Ret _ expr -> prPrec i 0 (concatD [doc (showString "return"), prt 0 expr, doc (showString ";")])
    AbsLatte.VRet _ -> prPrec i 0 (concatD [doc (showString "return"), doc (showString ";")])
    AbsLatte.Cond _ expr stmt -> prPrec i 0 (concatD [doc (showString "if"), doc (showString "("), prt 0 expr, doc (showString ")"), prt 0 stmt])
    AbsLatte.CondElse _ expr stmt1 stmt2 -> prPrec i 0 (concatD [doc (showString "if"), doc (showString "("), prt 0 expr, doc (showString ")"), prt 0 stmt1, doc (showString "else"), prt 0 stmt2])
    AbsLatte.While _ expr stmt -> prPrec i 0 (concatD [doc (showString "while"), doc (showString "("), prt 0 expr, doc (showString ")"), prt 0 stmt])
    AbsLatte.For _ type_ id expr stmt -> prPrec i 0 (concatD [doc (showString "for"), doc (showString "("), prt 0 type_, prt 0 id, doc (showString ":"), prt 0 expr, doc (showString ")"), prt 0 stmt])
    AbsLatte.SExp _ expr -> prPrec i 0 (concatD [prt 0 expr, doc (showString ";")])
  prtList _ [] = concatD []
  prtList _ (x:xs) = concatD [prt 0 x, prt 0 xs]

instance Print (AbsLatte.Item a) where
  prt i e = case e of
    AbsLatte.NoInit _ id -> prPrec i 0 (concatD [prt 0 id])
    AbsLatte.Init _ id expr -> prPrec i 0 (concatD [prt 0 id, doc (showString "="), prt 0 expr])
  prtList _ [x] = concatD [prt 0 x]
  prtList _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print [AbsLatte.Item a] where
  prt = prtList

instance Print (AbsLatte.Type a) where
  prt i e = case e of
    AbsLatte.Int _ -> prPrec i 0 (concatD [doc (showString "int")])
    AbsLatte.Str _ -> prPrec i 0 (concatD [doc (showString "string")])
    AbsLatte.Bool _ -> prPrec i 0 (concatD [doc (showString "boolean")])
    AbsLatte.Void _ -> prPrec i 0 (concatD [doc (showString "void")])
    AbsLatte.Struct _ id -> prPrec i 0 (concatD [prt 0 id])
    AbsLatte.Arr _ type_ -> prPrec i 0 (concatD [prt 0 type_, doc (showString "[]")])
    AbsLatte.Fun _ type_ types -> prPrec i 0 (concatD [prt 0 type_, doc (showString "("), prt 0 types, doc (showString ")")])
  prtList _ [] = concatD []
  prtList _ [x] = concatD [prt 0 x]
  prtList _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print [AbsLatte.Type a] where
  prt = prtList

instance Print (AbsLatte.Expr a) where
  prt i e = case e of
    AbsLatte.EVar _ id -> prPrec i 6 (concatD [prt 0 id])
    AbsLatte.ELitInt _ n -> prPrec i 6 (concatD [prt 0 n])
    AbsLatte.ELitTrue _ -> prPrec i 6 (concatD [doc (showString "true")])
    AbsLatte.ELitFalse _ -> prPrec i 6 (concatD [doc (showString "false")])
    AbsLatte.ESelf _ -> prPrec i 6 (concatD [doc (showString "self")])
    AbsLatte.EApp _ id exprs -> prPrec i 6 (concatD [prt 0 id, doc (showString "("), prt 0 exprs, doc (showString ")")])
    AbsLatte.EString _ str -> prPrec i 6 (concatD [prt 0 str])
    AbsLatte.EArr _ type_ expr -> prPrec i 6 (concatD [doc (showString "new"), prt 0 type_, doc (showString "["), prt 0 expr, doc (showString "]")])
    AbsLatte.EField _ expr id -> prPrec i 6 (concatD [prt 6 expr, doc (showString "."), prt 0 id])
    AbsLatte.EMthdApp _ expr id exprs -> prPrec i 6 (concatD [prt 6 expr, doc (showString "."), prt 0 id, doc (showString "("), prt 0 exprs, doc (showString ")")])
    AbsLatte.EIndex _ expr1 expr2 -> prPrec i 6 (concatD [prt 6 expr1, doc (showString "["), prt 0 expr2, doc (showString "]")])
    AbsLatte.EObject _ id -> prPrec i 5 (concatD [doc (showString "new"), prt 0 id])
    AbsLatte.ENull _ type_ -> prPrec i 6 (concatD [doc (showString "("), prt 0 type_, doc (showString ")null")])
    AbsLatte.Neg _ expr -> prPrec i 5 (concatD [doc (showString "-"), prt 6 expr])
    AbsLatte.Not _ expr -> prPrec i 5 (concatD [doc (showString "!"), prt 6 expr])
    AbsLatte.EMul _ expr1 mulop expr2 -> prPrec i 4 (concatD [prt 4 expr1, prt 0 mulop, prt 5 expr2])
    AbsLatte.EAdd _ expr1 addop expr2 -> prPrec i 3 (concatD [prt 3 expr1, prt 0 addop, prt 4 expr2])
    AbsLatte.ERel _ expr1 relop expr2 -> prPrec i 2 (concatD [prt 2 expr1, prt 0 relop, prt 3 expr2])
    AbsLatte.EAnd _ expr1 expr2 -> prPrec i 1 (concatD [prt 2 expr1, doc (showString "&&"), prt 1 expr2])
    AbsLatte.EOr _ expr1 expr2 -> prPrec i 0 (concatD [prt 1 expr1, doc (showString "||"), prt 0 expr2])
  prtList _ [] = concatD []
  prtList _ [x] = concatD [prt 0 x]
  prtList _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]

instance Print [AbsLatte.Expr a] where
  prt = prtList

instance Print (AbsLatte.AddOp a) where
  prt i e = case e of
    AbsLatte.Plus _ -> prPrec i 0 (concatD [doc (showString "+")])
    AbsLatte.Minus _ -> prPrec i 0 (concatD [doc (showString "-")])

instance Print (AbsLatte.MulOp a) where
  prt i e = case e of
    AbsLatte.Times _ -> prPrec i 0 (concatD [doc (showString "*")])
    AbsLatte.Div _ -> prPrec i 0 (concatD [doc (showString "/")])
    AbsLatte.Mod _ -> prPrec i 0 (concatD [doc (showString "%")])

instance Print (AbsLatte.RelOp a) where
  prt i e = case e of
    AbsLatte.LTH _ -> prPrec i 0 (concatD [doc (showString "<")])
    AbsLatte.LE _ -> prPrec i 0 (concatD [doc (showString "<=")])
    AbsLatte.GTH _ -> prPrec i 0 (concatD [doc (showString ">")])
    AbsLatte.GE _ -> prPrec i 0 (concatD [doc (showString ">=")])
    AbsLatte.EQU _ -> prPrec i 0 (concatD [doc (showString "==")])
    AbsLatte.NE _ -> prPrec i 0 (concatD [doc (showString "!=")])

