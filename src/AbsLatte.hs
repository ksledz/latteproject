-- Haskell data types for the abstract syntax.
-- Generated by the BNF converter.

{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module AbsLatte where

import Prelude (Char, Double, Integer, String, map, fmap)
import qualified Prelude as C (Eq, Ord, Show, Read, Functor)
import qualified Data.String

newtype Ident = Ident String
  deriving (C.Eq, C.Ord, C.Show, C.Read, Data.String.IsString)

data Program a = Program a [TopDef a]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

instance C.Functor Program where
    fmap f x = case x of
        Program a topdefs -> Program (f a) (map (fmap f) topdefs)

data TopDef a
    = FnDef a (Type a) Ident [Arg a] (Block a)
    | ClassDef a Ident [ClassItem a]
    | ClassEDef a Ident Ident [ClassItem a]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

instance C.Functor TopDef where
    fmap f x = case x of
        FnDef a type_ ident args block -> FnDef (f a) (fmap f type_) ident (map (fmap f) args) (fmap f block)
        ClassDef a ident classitems -> ClassDef (f a) ident (map (fmap f) classitems)
        ClassEDef a ident1 ident2 classitems -> ClassEDef (f a) ident1 ident2 (map (fmap f) classitems)

data ClassItem a
    = FieldDef a (Type a) Ident
    | MethodDef a (Type a) Ident [Arg a] (Block a)
  deriving (C.Eq, C.Ord, C.Show, C.Read)

instance C.Functor ClassItem where
    fmap f x = case x of
        FieldDef a type_ ident -> FieldDef (f a) (fmap f type_) ident
        MethodDef a type_ ident args block -> MethodDef (f a) (fmap f type_) ident (map (fmap f) args) (fmap f block)

data Arg a = Arg a (Type a) Ident
  deriving (C.Eq, C.Ord, C.Show, C.Read)

instance C.Functor Arg where
    fmap f x = case x of
        Arg a type_ ident -> Arg (f a) (fmap f type_) ident

data Block a = Block a [Stmt a]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

instance C.Functor Block where
    fmap f x = case x of
        Block a stmts -> Block (f a) (map (fmap f) stmts)

data Stmt a
    = Empty a
    | BStmt a (Block a)
    | Decl a (Type a) [Item a]
    | Ass a (Expr a) (Expr a)
    | Incr a (Expr a)
    | Decr a (Expr a)
    | Ret a (Expr a)
    | VRet a
    | Cond a (Expr a) (Stmt a)
    | CondElse a (Expr a) (Stmt a) (Stmt a)
    | While a (Expr a) (Stmt a)
    | For a (Type a) Ident (Expr a) (Stmt a)
    | SExp a (Expr a)
  deriving (C.Eq, C.Ord, C.Show, C.Read)

instance C.Functor Stmt where
    fmap f x = case x of
        Empty a -> Empty (f a)
        BStmt a block -> BStmt (f a) (fmap f block)
        Decl a type_ items -> Decl (f a) (fmap f type_) (map (fmap f) items)
        Ass a expr1 expr2 -> Ass (f a) (fmap f expr1) (fmap f expr2)
        Incr a expr -> Incr (f a) (fmap f expr)
        Decr a expr -> Decr (f a) (fmap f expr)
        Ret a expr -> Ret (f a) (fmap f expr)
        VRet a -> VRet (f a)
        Cond a expr stmt -> Cond (f a) (fmap f expr) (fmap f stmt)
        CondElse a expr stmt1 stmt2 -> CondElse (f a) (fmap f expr) (fmap f stmt1) (fmap f stmt2)
        While a expr stmt -> While (f a) (fmap f expr) (fmap f stmt)
        For a type_ ident expr stmt -> For (f a) (fmap f type_) ident (fmap f expr) (fmap f stmt)
        SExp a expr -> SExp (f a) (fmap f expr)

data Item a = NoInit a Ident | Init a Ident (Expr a)
  deriving (C.Eq, C.Ord, C.Show, C.Read)

instance C.Functor Item where
    fmap f x = case x of
        NoInit a ident -> NoInit (f a) ident
        Init a ident expr -> Init (f a) ident (fmap f expr)

data Type a
    = Int a
    | Str a
    | Bool a
    | Void a
    | Struct a Ident
    | Arr a (Type a)
    | Fun a (Type a) [Type a]
  deriving (C.Eq, C.Ord, C.Show, C.Read)

instance C.Functor Type where
    fmap f x = case x of
        Int a -> Int (f a)
        Str a -> Str (f a)
        Bool a -> Bool (f a)
        Void a -> Void (f a)
        Struct a ident -> Struct (f a) ident
        Arr a type_ -> Arr (f a) (fmap f type_)
        Fun a type_ types -> Fun (f a) (fmap f type_) (map (fmap f) types)

data Expr a
    = EVar a Ident
    | ELitInt a Integer
    | ELitTrue a
    | ELitFalse a
    | ESelf a
    | EApp a Ident [Expr a]
    | EString a String
    | EArr a (Type a) (Expr a)
    | EField a (Expr a) Ident
    | EMthdApp a (Expr a) Ident [Expr a]
    | EIndex a (Expr a) (Expr a)
    | EObject a Ident
    | ENull a (Expr a)
    | Neg a (Expr a)
    | Not a (Expr a)
    | EMul a (Expr a) (MulOp a) (Expr a)
    | EAdd a (Expr a) (AddOp a) (Expr a)
    | ERel a (Expr a) (RelOp a) (Expr a)
    | EAnd a (Expr a) (Expr a)
    | EOr a (Expr a) (Expr a)
  deriving (C.Eq, C.Ord, C.Show, C.Read)

instance C.Functor Expr where
    fmap f x = case x of
        EVar a ident -> EVar (f a) ident
        ELitInt a integer -> ELitInt (f a) integer
        ELitTrue a -> ELitTrue (f a)
        ELitFalse a -> ELitFalse (f a)
        ESelf a -> ESelf (f a)
        EApp a ident exprs -> EApp (f a) ident (map (fmap f) exprs)
        EString a string -> EString (f a) string
        EArr a type_ expr -> EArr (f a) (fmap f type_) (fmap f expr)
        EField a expr ident -> EField (f a) (fmap f expr) ident
        EMthdApp a expr ident exprs -> EMthdApp (f a) (fmap f expr) ident (map (fmap f) exprs)
        EIndex a expr1 expr2 -> EIndex (f a) (fmap f expr1) (fmap f expr2)
        EObject a ident -> EObject (f a) ident
        ENull a expr -> ENull (f a) (fmap f expr)
        Neg a expr -> Neg (f a) (fmap f expr)
        Not a expr -> Not (f a) (fmap f expr)
        EMul a expr1 mulop expr2 -> EMul (f a) (fmap f expr1) (fmap f mulop) (fmap f expr2)
        EAdd a expr1 addop expr2 -> EAdd (f a) (fmap f expr1) (fmap f addop) (fmap f expr2)
        ERel a expr1 relop expr2 -> ERel (f a) (fmap f expr1) (fmap f relop) (fmap f expr2)
        EAnd a expr1 expr2 -> EAnd (f a) (fmap f expr1) (fmap f expr2)
        EOr a expr1 expr2 -> EOr (f a) (fmap f expr1) (fmap f expr2)

data AddOp a = Plus a | Minus a
  deriving (C.Eq, C.Ord, C.Show, C.Read)

instance C.Functor AddOp where
    fmap f x = case x of
        Plus a -> Plus (f a)
        Minus a -> Minus (f a)

data MulOp a = Times a | Div a | Mod a
  deriving (C.Eq, C.Ord, C.Show, C.Read)

instance C.Functor MulOp where
    fmap f x = case x of
        Times a -> Times (f a)
        Div a -> Div (f a)
        Mod a -> Mod (f a)

data RelOp a = LTH a | LE a | GTH a | GE a | EQU a | NE a
  deriving (C.Eq, C.Ord, C.Show, C.Read)

instance C.Functor RelOp where
    fmap f x = case x of
        LTH a -> LTH (f a)
        LE a -> LE (f a)
        GTH a -> GTH (f a)
        GE a -> GE (f a)
        EQU a -> EQU (f a)
        NE a -> NE (f a)

