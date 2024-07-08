module SessionPi.Syntax where

import Bisimulation (Bisimulation (behave))

data Proc where
    Snd :: String -> Val -> Proc -> Proc
    Rec :: Qualifier -> String -> String -> Proc -> Proc
    Par :: Proc -> Proc -> Proc
    Brn :: Val -> Proc -> Proc -> Proc
    Nil :: Proc
    Bnd :: BoundVar -> BoundVar -> Proc -> Proc
    deriving (Show, Eq)

data Val where
    Var :: String -> Val
    Lit :: Bool -> Val
    deriving (Show, Eq)

type BoundVar = (String, Maybe SpiType) -- type declaration is optional

isVar :: Val -> Bool
isVar (Var _) = True
isVar _ = False

isLit :: Val -> Bool
isLit (Lit _) = True
isLit _ = False

unvar :: Val -> String
unvar (Var x) = x
unvar _ = undefined

unlit :: Val -> Bool
unlit (Lit l) = l
unlit _ = undefined

-- TYPES

data Qualifier where
    Lin :: Qualifier
    Un  :: Qualifier
    deriving (Show, Eq, Ord)

data Pretype where
    Receiving :: SpiType -> SpiType -> Pretype
    Sending   :: SpiType -> SpiType -> Pretype
    deriving (Eq, Ord)

instance Show Pretype where
    show :: Pretype -> String
    show (Receiving t1 t2) = "?(" ++ show t1 ++ ") ." ++ show t2
    show (Sending t1 t2) = "!(" ++ show t1 ++ ") ." ++ show t2

argument :: Pretype -> SpiType
argument (Receiving a _) = a
argument (Sending a _)   = a

thenProcess :: Pretype -> SpiType
thenProcess (Receiving _ p) = p
thenProcess (Sending _ p)   = p

data SpiType where
    Boolean   :: SpiType
    End       :: SpiType
    Qualified :: Qualifier -> Pretype -> SpiType
    TypeVar   :: String -> SpiType
    Recursive :: String -> SpiType -> SpiType
    deriving (Eq, Ord) -- intensional equality defined here

instance Show SpiType where
    show :: SpiType -> String
    show Boolean = "bool"
    show End = "end"
    show (Qualified q p) = show q ++ " " ++ show p
    show (TypeVar t) = t
    show (Recursive v p) = "rec " ++ v ++ " " ++ show p


dualType :: SpiType -> SpiType
dualType End = End
dualType Boolean = error "Duality is undefined for the bool type. Perhaps you tried to type a process as a boolean?"
dualType (Qualified q (Receiving t1 t2)) = Qualified q (Sending t1 (dualType t2))
dualType (Qualified q (Sending t1 t2)) = Qualified q (Receiving t1 (dualType t2))
dualType (Recursive a p) = Recursive a (dualType p)
dualType (TypeVar x) = TypeVar x

class Restrictable t where
    predicate :: Qualifier -> t -> Bool

instance Restrictable SpiType where
    predicate :: Qualifier -> SpiType -> Bool
    predicate Un (Qualified Lin _) = False
    predicate _ _                  = True

instance (Restrictable t, Foldable f) => Restrictable (f t) where
    predicate :: Qualifier -> f t -> Bool
    predicate = all . predicate

subsType :: String -> SpiType -> SpiType -> SpiType
subsType x t (TypeVar y) | x == y = t
subsType x t (Qualified q (Sending t1 t2)) = Qualified q (Sending (subsType x t t1) (subsType x t t2))
subsType x t (Qualified q (Receiving t1 t2)) = Qualified q (Receiving (subsType x t t1) (subsType x t t2))
subsType _ _ t = t

instance Bisimulation SpiType where
    behave :: SpiType -> (SpiType, SpiType)
    behave (Qualified q (Sending v t)) = (t, Qualified q (Sending v End))
    behave (Qualified q (Receiving v t)) = (t, Qualified q (Receiving v End))
    behave t@(Recursive x t') = behave (subsType x t t')
    behave t = (t, t)

{-
>>>subsType "x" (Recursive "x" (Qualified Un (Sending Boolean (TypeVar "x")))) (Qualified Un (Sending Boolean (TypeVar "x")))
Qualified Un (Sending Boolean (Recursive "x" (Qualified Un (Sending Boolean (TypeVar "x")))))
>>>behave 
>>>behave (Recursive "x" (Qualified Un (Sending Boolean (TypeVar "x"))))
Just (Recursive "x" (Qualified Un (Sending Boolean (TypeVar "x"))),Qualified Un (Sending Boolean End))
-}

