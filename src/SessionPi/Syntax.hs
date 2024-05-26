module SessionPi.Syntax where

import Bisimulation (Bisimulation (behave))

data Proc where
    Snd :: String -> Val -> Proc -> Proc
    Rec :: String -> String -> Proc -> Proc
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

{- class Expr a where
    fv :: a -> S.Set String
    substitute :: a -> Val -> String -> a

instance Expr Val where
    fv :: Val -> S.Set String
    fv (Var x) = S.singleton x
    fv (Lit _) = mempty
    substitute :: Val -> Val -> String -> Val
    substitute (Lit l) _ _ = Lit l
    substitute t@(Var x) v y
        | x == y    = v
        | otherwise = t


instance Expr Proc where
    fv :: Proc -> S.Set String
    fv Nil = mempty
    fv (Par p1 p2) = fv p1 `S.union` fv p2
    fv (Snd x v p) = fv v `S.union` S.insert x (fv p)
    fv (Rec x y p) = S.insert x $ S.delete y $ fv p
    fv (Brn v p1 p2) = fv v `S.union` fv p1 `S.union` fv p2
    fv (Bnd x y p) = S.delete x $ S.delete y $ fv p
    substitute :: Proc -> Val -> String -> Proc
    substitute Nil _ _ = Nil
    substitute (Par p1 p2) v x = Par (substitute p1 v x) (substitute p2 v x)
    substitute (Snd y u p) v x = Snd y' u' p'
        where
            y'  | x == y    = unvar v
                | otherwise = y
            u'  = substitute u v x
            p'  = substitute p v x
    substitute (Rec y z p) v x = Rec y' z p'
        where
            y'  | x == y    = unvar v
                | otherwise = y
            -- z'  = z -- perché non è una fv
            p'  | x == z    = p
                | otherwise = substitute p v x
    substitute (Brn g p1 p2) v x = Brn g' p1' p2'
        where
            g'  = substitute g v x
            p1' = substitute p1 v x
            p2' = substitute p2 v x
    substitute (Bnd y z p) v x = Bnd y z p'
        where
            -- y' = y -- perché non è una fv
            -- z' = z -- perché non è una fv
            p'  | x == z || x == y  = p
                | otherwise         = substitute p v x -}

-- bind is active in all parallel branches by definition, equivalently here we lift it to the parent node
-- inefficiente ma vabbè
preprocess :: Proc -> Proc
preprocess (Par p1 p2) = b1 $ b2 p'
    where
        (b1, p1') = case p1 of
                Bnd x y p -> (Bnd x y . preprocess, p)
                _         -> (id, p1)
        (b2, p2') = case p2 of
                Bnd x y p -> (Bnd x y . preprocess, p)
                _         -> (id, p2)
        p' = Par (preprocess p1') (preprocess p2')
preprocess Nil = Nil
preprocess (Snd x y p) = Snd x y (preprocess p)
preprocess (Rec x y p) = Rec x y (preprocess p)
preprocess (Bnd x y p) = Bnd x y (preprocess p)
preprocess (Brn g p1 p2) = Brn g (preprocess p1) (preprocess p2)

-- TYPES

data Qualifier where
    Lin :: Qualifier
    Un  :: Qualifier
    deriving (Show, Eq, Ord)

data Pretype where
    Receiving :: SpiType -> SpiType -> Pretype
    Sending   :: SpiType -> SpiType -> Pretype
    deriving (Show, Eq, Ord)


data SpiType where
    Boolean   :: SpiType
    End       :: SpiType
    Qualified :: Qualifier -> Pretype -> SpiType
    TypeVar   :: String -> SpiType
    Recursive :: String -> SpiType -> SpiType
    deriving (Show, Eq, Ord) -- intensional equality defined here

dualType :: SpiType -> SpiType
dualType End = End
dualType Boolean = error "Duality is undefined for the bool type. Perhaps you tried to type a process as a boolean?"
dualType (Qualified q (Receiving t1 t2)) = Qualified q (Sending t1 (dualType t2))
dualType (Qualified q (Sending t1 t2)) = Qualified q (Receiving t1 (dualType t2))
dualType (Recursive a p) = Recursive a (dualType p)
dualType (TypeVar x) = TypeVar x

class Unrestricted t where
    unrestricted :: t -> Bool

instance Unrestricted SpiType where
    unrestricted :: SpiType -> Bool
    unrestricted (Qualified Lin _)  = False
    unrestricted _                  = True

instance (Unrestricted t, Foldable f) => Unrestricted (f t) where
    unrestricted :: f t -> Bool
    unrestricted = all unrestricted

subsType :: String -> SpiType -> SpiType -> SpiType
subsType x t (TypeVar y) | x == y = t
subsType x t (Qualified q (Sending t1 t2)) = Qualified q (Sending (subsType x t t1) (subsType x t t2))
subsType x t (Qualified q (Receiving t1 t2)) = Qualified q (Receiving (subsType x t t1) (subsType x t t2))
subsType _ _ t = t

instance Bisimulation SpiType where
    behave :: SpiType -> Maybe (SpiType, SpiType)
    behave (Qualified q (Sending v t)) = Just (t, Qualified q (Sending v End))
    behave (Qualified q (Receiving v t)) = Just (t, Qualified q (Receiving v End))
    behave t@(Recursive x t') = behave (subsType x t t')
    behave t = Just (t, t)

{-
>>>subsType "x" (Recursive "x" (Qualified Un (Sending Boolean (TypeVar "x")))) (Qualified Un (Sending Boolean (TypeVar "x")))
Qualified Un (Sending Boolean (Recursive "x" (Qualified Un (Sending Boolean (TypeVar "x")))))
>>>behave 
>>>behave (Recursive "x" (Qualified Un (Sending Boolean (TypeVar "x"))))
Just (Recursive "x" (Qualified Un (Sending Boolean (TypeVar "x"))),Qualified Un (Sending Boolean End))
-}
