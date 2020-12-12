-- This Happy file was machine-generated by the BNF converter
{
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
module ParLatte where
import qualified AbsLatte
import LexLatte
}

%name pProgram_internal Program
-- no lexer declaration
%monad { Either String } { (>>=) } { return }
%tokentype {Token}
%token
  '!' { PT _ (TS _ 1) }
  '!=' { PT _ (TS _ 2) }
  '%' { PT _ (TS _ 3) }
  '&&' { PT _ (TS _ 4) }
  '(' { PT _ (TS _ 5) }
  ')' { PT _ (TS _ 6) }
  '*' { PT _ (TS _ 7) }
  '+' { PT _ (TS _ 8) }
  '++' { PT _ (TS _ 9) }
  ',' { PT _ (TS _ 10) }
  '-' { PT _ (TS _ 11) }
  '--' { PT _ (TS _ 12) }
  '/' { PT _ (TS _ 13) }
  ';' { PT _ (TS _ 14) }
  '<' { PT _ (TS _ 15) }
  '<=' { PT _ (TS _ 16) }
  '=' { PT _ (TS _ 17) }
  '==' { PT _ (TS _ 18) }
  '>' { PT _ (TS _ 19) }
  '>=' { PT _ (TS _ 20) }
  '[' { PT _ (TS _ 21) }
  '[]' { PT _ (TS _ 22) }
  ']' { PT _ (TS _ 23) }
  'boolean' { PT _ (TS _ 24) }
  'else' { PT _ (TS _ 25) }
  'false' { PT _ (TS _ 26) }
  'if' { PT _ (TS _ 27) }
  'int' { PT _ (TS _ 28) }
  'new' { PT _ (TS _ 29) }
  'return' { PT _ (TS _ 30) }
  'string' { PT _ (TS _ 31) }
  'true' { PT _ (TS _ 32) }
  'void' { PT _ (TS _ 33) }
  'while' { PT _ (TS _ 34) }
  '{' { PT _ (TS _ 35) }
  '||' { PT _ (TS _ 36) }
  '}' { PT _ (TS _ 37) }
  L_Ident  { PT _ (TV _) }
  L_integ  { PT _ (TI _) }
  L_quoted { PT _ (TL _) }

%%

Ident :: { (Maybe (Int, Int), AbsLatte.Ident) }
Ident  : L_Ident { (Just (tokenLineCol $1), AbsLatte.Ident (tokenText $1)) }

Integer :: { (Maybe (Int, Int), Integer) }
Integer  : L_integ  { (Just (tokenLineCol $1), (read ((tokenText $1))) :: Integer) }

String  :: { (Maybe (Int, Int), String) }
String   : L_quoted { (Just (tokenLineCol $1), (tokenText $1)) }

Program :: { (Maybe (Int, Int),  (AbsLatte.Program (Maybe (Int, Int))) ) }
Program : ListTopDef { (fst $1, AbsLatte.Program (fst $1) (snd $1)) }

TopDef :: { (Maybe (Int, Int),  (AbsLatte.TopDef (Maybe (Int, Int))) ) }
TopDef : Type Ident '(' ListArg ')' Block { (fst $1, AbsLatte.FnDef (fst $1) (snd $1) (snd $2) (snd $4) (snd $6)) }

ListTopDef :: { (Maybe (Int, Int),  [AbsLatte.TopDef (Maybe (Int, Int))] ) }
ListTopDef : TopDef { (fst $1, (:[]) (snd $1)) }
           | TopDef ListTopDef { (fst $1, (:) (snd $1) (snd $2)) }

Arg :: { (Maybe (Int, Int),  (AbsLatte.Arg (Maybe (Int, Int))) ) }
Arg : Type Ident { (fst $1, AbsLatte.Arg (fst $1) (snd $1) (snd $2)) }

ListArg :: { (Maybe (Int, Int),  [AbsLatte.Arg (Maybe (Int, Int))] ) }
ListArg : {- empty -} { (Nothing, []) }
        | Arg { (fst $1, (:[]) (snd $1)) }
        | Arg ',' ListArg { (fst $1, (:) (snd $1) (snd $3)) }

Block :: { (Maybe (Int, Int),  (AbsLatte.Block (Maybe (Int, Int))) ) }
Block : '{' ListStmt '}' { (Just (tokenLineCol $1), AbsLatte.Block (Just (tokenLineCol $1)) (snd $2)) }

ListStmt :: { (Maybe (Int, Int),  [AbsLatte.Stmt (Maybe (Int, Int))] ) }
ListStmt : {- empty -} { (Nothing, []) }
         | Stmt ListStmt { (fst $1, (:) (snd $1) (snd $2)) }

Stmt :: { (Maybe (Int, Int),  (AbsLatte.Stmt (Maybe (Int, Int))) ) }
Stmt : ';' { (Just (tokenLineCol $1), AbsLatte.Empty (Just (tokenLineCol $1))) }
     | Block { (fst $1, AbsLatte.BStmt (fst $1) (snd $1)) }
     | Type ListItem ';' { (fst $1, AbsLatte.Decl (fst $1) (snd $1) (snd $2)) }
     | Ident '=' Expr ';' { (fst $1, AbsLatte.Ass (fst $1) (snd $1) (snd $3)) }
     | Ident '++' ';' { (fst $1, AbsLatte.Incr (fst $1) (snd $1)) }
     | Ident '--' ';' { (fst $1, AbsLatte.Decr (fst $1) (snd $1)) }
     | 'return' Expr ';' { (Just (tokenLineCol $1), AbsLatte.Ret (Just (tokenLineCol $1)) (snd $2)) }
     | 'return' ';' { (Just (tokenLineCol $1), AbsLatte.VRet (Just (tokenLineCol $1))) }
     | 'if' '(' Expr ')' Stmt { (Just (tokenLineCol $1), AbsLatte.Cond (Just (tokenLineCol $1)) (snd $3) (snd $5)) }
     | 'if' '(' Expr ')' Stmt 'else' Stmt { (Just (tokenLineCol $1), AbsLatte.CondElse (Just (tokenLineCol $1)) (snd $3) (snd $5) (snd $7)) }
     | 'while' '(' Expr ')' Stmt { (Just (tokenLineCol $1), AbsLatte.While (Just (tokenLineCol $1)) (snd $3) (snd $5)) }
     | Expr ';' { (fst $1, AbsLatte.SExp (fst $1) (snd $1)) }

Item :: { (Maybe (Int, Int),  (AbsLatte.Item (Maybe (Int, Int))) ) }
Item : Ident { (fst $1, AbsLatte.NoInit (fst $1) (snd $1)) }
     | Ident '=' Expr { (fst $1, AbsLatte.Init (fst $1) (snd $1) (snd $3)) }

ListItem :: { (Maybe (Int, Int),  [AbsLatte.Item (Maybe (Int, Int))] ) }
ListItem : Item { (fst $1, (:[]) (snd $1)) }
         | Item ',' ListItem { (fst $1, (:) (snd $1) (snd $3)) }

Type :: { (Maybe (Int, Int),  (AbsLatte.Type (Maybe (Int, Int))) ) }
Type : 'int' { (Just (tokenLineCol $1), AbsLatte.Int (Just (tokenLineCol $1))) }
     | 'string' { (Just (tokenLineCol $1), AbsLatte.Str (Just (tokenLineCol $1))) }
     | 'boolean' { (Just (tokenLineCol $1), AbsLatte.Bool (Just (tokenLineCol $1))) }
     | 'void' { (Just (tokenLineCol $1), AbsLatte.Void (Just (tokenLineCol $1))) }
     | Type '[]' { (fst $1, AbsLatte.Arr (fst $1) (snd $1)) }

ListType :: { (Maybe (Int, Int),  [AbsLatte.Type (Maybe (Int, Int))] ) }
ListType : {- empty -} { (Nothing, []) }
         | Type { (fst $1, (:[]) (snd $1)) }
         | Type ',' ListType { (fst $1, (:) (snd $1) (snd $3)) }

Expr6 :: { (Maybe (Int, Int),  AbsLatte.Expr (Maybe (Int, Int)) ) }
Expr6 : Ident { (fst $1, AbsLatte.EVar (fst $1) (snd $1)) }
      | Integer { (fst $1, AbsLatte.ELitInt (fst $1) (snd $1)) }
      | 'true' { (Just (tokenLineCol $1), AbsLatte.ELitTrue (Just (tokenLineCol $1))) }
      | 'false' { (Just (tokenLineCol $1), AbsLatte.ELitFalse (Just (tokenLineCol $1))) }
      | Ident '(' ListExpr ')' { (fst $1, AbsLatte.EApp (fst $1) (snd $1) (snd $3)) }
      | String { (fst $1, AbsLatte.EString (fst $1) (snd $1)) }
      | 'new' Type '[' Expr ']' { (Just (tokenLineCol $1), AbsLatte.EArr (Just (tokenLineCol $1)) (snd $2) (snd $4)) }
      | '(' Expr ')' { (Just (tokenLineCol $1), (snd $2)) }

Expr5 :: { (Maybe (Int, Int),  AbsLatte.Expr (Maybe (Int, Int)) ) }
Expr5 : '-' Expr6 { (Just (tokenLineCol $1), AbsLatte.Neg (Just (tokenLineCol $1)) (snd $2)) }
      | '!' Expr6 { (Just (tokenLineCol $1), AbsLatte.Not (Just (tokenLineCol $1)) (snd $2)) }
      | Expr6 { (fst $1, (snd $1)) }

Expr4 :: { (Maybe (Int, Int),  AbsLatte.Expr (Maybe (Int, Int)) ) }
Expr4 : Expr4 MulOp Expr5 { (fst $1, AbsLatte.EMul (fst $1) (snd $1) (snd $2) (snd $3)) }
      | Expr5 { (fst $1, (snd $1)) }

Expr3 :: { (Maybe (Int, Int),  AbsLatte.Expr (Maybe (Int, Int)) ) }
Expr3 : Expr3 AddOp Expr4 { (fst $1, AbsLatte.EAdd (fst $1) (snd $1) (snd $2) (snd $3)) }
      | Expr4 { (fst $1, (snd $1)) }

Expr2 :: { (Maybe (Int, Int),  AbsLatte.Expr (Maybe (Int, Int)) ) }
Expr2 : Expr2 RelOp Expr3 { (fst $1, AbsLatte.ERel (fst $1) (snd $1) (snd $2) (snd $3)) }
      | Expr3 { (fst $1, (snd $1)) }

Expr1 :: { (Maybe (Int, Int),  AbsLatte.Expr (Maybe (Int, Int)) ) }
Expr1 : Expr2 '&&' Expr1 { (fst $1, AbsLatte.EAnd (fst $1) (snd $1) (snd $3)) }
      | Expr2 { (fst $1, (snd $1)) }

Expr :: { (Maybe (Int, Int),  (AbsLatte.Expr (Maybe (Int, Int))) ) }
Expr : Expr1 '||' Expr { (fst $1, AbsLatte.EOr (fst $1) (snd $1) (snd $3)) }
     | Expr1 { (fst $1, (snd $1)) }

ListExpr :: { (Maybe (Int, Int),  [AbsLatte.Expr (Maybe (Int, Int))] ) }
ListExpr : {- empty -} { (Nothing, []) }
         | Expr { (fst $1, (:[]) (snd $1)) }
         | Expr ',' ListExpr { (fst $1, (:) (snd $1) (snd $3)) }

AddOp :: { (Maybe (Int, Int),  (AbsLatte.AddOp (Maybe (Int, Int))) ) }
AddOp : '+' { (Just (tokenLineCol $1), AbsLatte.Plus (Just (tokenLineCol $1))) }
      | '-' { (Just (tokenLineCol $1), AbsLatte.Minus (Just (tokenLineCol $1))) }

MulOp :: { (Maybe (Int, Int),  (AbsLatte.MulOp (Maybe (Int, Int))) ) }
MulOp : '*' { (Just (tokenLineCol $1), AbsLatte.Times (Just (tokenLineCol $1))) }
      | '/' { (Just (tokenLineCol $1), AbsLatte.Div (Just (tokenLineCol $1))) }
      | '%' { (Just (tokenLineCol $1), AbsLatte.Mod (Just (tokenLineCol $1))) }

RelOp :: { (Maybe (Int, Int),  (AbsLatte.RelOp (Maybe (Int, Int))) ) }
RelOp : '<' { (Just (tokenLineCol $1), AbsLatte.LTH (Just (tokenLineCol $1))) }
      | '<=' { (Just (tokenLineCol $1), AbsLatte.LE (Just (tokenLineCol $1))) }
      | '>' { (Just (tokenLineCol $1), AbsLatte.GTH (Just (tokenLineCol $1))) }
      | '>=' { (Just (tokenLineCol $1), AbsLatte.GE (Just (tokenLineCol $1))) }
      | '==' { (Just (tokenLineCol $1), AbsLatte.EQU (Just (tokenLineCol $1))) }
      | '!=' { (Just (tokenLineCol $1), AbsLatte.NE (Just (tokenLineCol $1))) }
{

happyError :: [Token] -> Either String a
happyError ts = Left $
  "syntax error at " ++ tokenPos ts ++
  case ts of
    []      -> []
    [Err _] -> " due to lexer error"
    t:_     -> " before `" ++ (prToken t) ++ "'"

myLexer = tokens
pProgram = (>>= return . snd) . pProgram_internal
}
