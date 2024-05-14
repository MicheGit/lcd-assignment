module SessionPi.Language where

import qualified Data.Set as S
import qualified Data.Map as M
import Data.Maybe (fromJust)
import Control.Parallel.Strategies (runEval, evalList, rdeepseq, using)
import Data.Either (isRight)

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

data Qualifier where
    Lin :: Qualifier
    Un  :: Qualifier
    deriving (Show, Eq)

data Pretype where
    Receiving :: SpiType -> SpiType -> Pretype
    Sending   :: SpiType -> SpiType -> Pretype
    deriving (Show, Eq)

data SpiType where
    Boolean   :: SpiType
    End       :: SpiType
    Qualified :: Qualifier -> Pretype -> SpiType
    deriving (Show, Eq)

type Context = M.Map String SpiType

dualType :: SpiType -> SpiType
dualType End = End
dualType Boolean = error "Duality is undefinde for boolean. Perhaps you tried to type a process as a boolean?"
dualType (Qualified q (Receiving t1 t2)) = Qualified q (Sending t1 (dualType t2))
dualType (Qualified q (Sending t1 t2)) = Qualified q (Receiving t1 (dualType t2))

class Unrestricted t where
    unrestricted :: t -> Bool

instance Unrestricted SpiType where
    unrestricted :: SpiType -> Bool
    unrestricted (Qualified Lin _)  = False
    unrestricted _                  = True

instance (Unrestricted t, Foldable f) => Unrestricted (f t) where
    unrestricted :: f t -> Bool
    unrestricted = all unrestricted

getUnrestricted :: Context -> Context
getUnrestricted = M.filter unrestricted

ndsplit :: Context -> [(Context, Context)]
ndsplit ctx | M.size ctx == 0 = [(mempty, mempty)]
ndsplit ctx =
    let unr = getUnrestricted ctx
        lin = M.difference ctx unr
        lins :: [Context]
        lins =
            (M.fromArgSet <$>) $
            S.toList $       -- for all the       -- for all the       -- for all the       -- for all the       -- for all the       -- for all the       -- for all the       -- for all the       -- for all the       -- for all the       -- for all the       -- for all the       -- for all the       -- for all the       -- for all the       -- for all the
                   -- for all the
                   -- for all the
                   -- for all the
                   -- for all the
                   -- for all the       -- for all the       -- for all the       -- for all the
                   -- for all the
            S.powerSet $     -- possible combination of     -- possible combination of     -- possible combination of     -- possible combination of     -- possible combination of     -- possible combination of     -- possible combination of     -- possible combination of     -- possible combination of
            M.argSet lin     -- (claims with) linearly qualified types

     in [(unr `M.union` comb, unr `M.union` (lin `M.difference` comb)) | comb <- lins]
     -- all possible splits

update :: String -> SpiType ->  Context -> Context
update k t ctx
    | not (k `M.member` ctx) = M.insert k t ctx
    | fromJust (M.lookup k ctx) == t = ctx -- we let go unrestricted types to be claimed multiple times
    | otherwise              = error "Tryed to update a contex with a yet existing variable or to reintroduce a linear variable"

extract :: String -> Context -> Maybe (Context, SpiType)
extract x ctx = do
    t <- M.lookup x ctx
    let ctx' = if unrestricted t
        then ctx
        else M.delete x ctx
    return (ctx', t)


type Claim = (Val, SpiType)

type TypeErrorBundle = String

class TypeCheck a where
    -- TODO better errors
    typeCheck :: Context -> a -> Either TypeErrorBundle ()

instance TypeCheck Claim where
    typeCheck :: Context -> Claim -> Either TypeErrorBundle ()
    typeCheck ctx (Lit _, Boolean)
        | unrestricted ctx = Right ()
        | otherwise        = Left ("Failed to type context, there are unused linear channels ctx=" ++ show ctx)
    typeCheck ctx (Var x, t)
        | M.lookup x ctx == Just t && unrestricted ctx' = Right ()
        | not $ unrestricted ctx'                       = Left "Failed to type context, there are unused linear channels"
        | otherwise                                     = Left "Variable not found or differently typed in contex"
        where
            ctx' = M.delete x ctx
    typeCheck _ _ = Left "Ill typed variable"

instance TypeCheck Proc where
    typeCheck :: Context -> Proc -> Either TypeErrorBundle ()
    typeCheck ctx Nil
        | unrestricted ctx = Right ()
        | otherwise        = Left ("Failed to type context, there are unused linear channels ctx=" ++ show ctx)
    typeCheck ctx (Par p1 p2) =
        let splits = ndsplit ctx
            candidates = (\(ctx1, ctx2) -> do
                typeCheck ctx1 p1
                typeCheck ctx2 p2) <$> splits
            result = candidates `using` evalList rdeepseq
         in if any isRight result
            then Right ()
            else Left ("No context split could type the requested process\n" ++ show splits ++ "\n" ++ show ctx)
    typeCheck ctx (Bnd (x, Just tx) (y, Just ty) p) = typeCheck (update x tx $ update y ty ctx) p
    typeCheck _   (Bnd {}) = Left "Bind without type annotations"
    typeCheck ctx (Brn g p1 p2) = do -- here we can optimize and not rely on parallelization
        let guardCtx = getUnrestricted ctx -- the only context that could type a boolean variable is unrestricted
        typeCheck guardCtx (g, Boolean)
        typeCheck ctx p1
        typeCheck ctx p2
    typeCheck ctx (Rec x y p) = do            -- here we can optimize
        (ctx', t, u) <- case extract x ctx of    -- if there is not, error
                Just (c, Qualified _ (Receiving t u)) -> Right (c, t, u)
                _                                       -> Left "Receiving channel not defined or ill-defined"
        -- ctx types channel x
        -- no need to check for unrestrictedness of gamma1
        -- as gamma2 we just need to use ctx'
        typeCheck (M.insert y t $ update x u ctx') p
    typeCheck ctx (Snd x v p) = do -- similar to recceive we can optimize
        (ctx', t, u) <- case extract x ctx of    -- if there is not, error
                Just (c, Qualified _ (Sending t u)) -> Right (c, t, u)
                Nothing -> Left ("Sending channel not defined"  ++ x ++ " ctx=" ++ show ctx)
                _ -> Left ("Sending channel ill defined" ++ x ++ " ctx=" ++ show ctx)
        ctx'' <- case (v, t) of
                (Var y, Qualified Lin _) -> case extract y ctx' of
                        Just (c, t') -> if t == t'
                            then Right c
                            else Left "Inconsistent types"
                        Nothing -> Left "Undefined linear channel"
                _ -> do
                    typeCheck (getUnrestricted ctx') (v, t)
                    Right ctx'
        typeCheck (update x u ctx'') p





