module SessionPi.Language.Types where
import SessionPi.Language

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Applicative (Alternative(empty, (<|>)))
import Control.Monad (unless, guard)
import GHC.Base (when)
import Control.Parallel.Strategies (using, evalList, rdeepseq)
import Text.Megaparsec (choice)
import ForkJoin (forkJoin)

type Context = M.Map String SpiType

type TypeErrorBundle = String

newtype CT a = CT (Context -> Either TypeErrorBundle (a, Context))

unwrap :: CT a -> Context -> Either TypeErrorBundle (a, Context)
unwrap (CT f) = f

instance Functor CT where
    fmap f (CT fa) = CT (\c -> do
        (a, c') <- fa c
        return (f a, c'))

instance Applicative CT where
    pure x = CT (\c -> Right (x, c))
    CT fn <*> CT fa = CT (\c -> do
        (f, c')  <- fn c
        (a, c'') <- fa c' 
        return (f a, c''))

instance Monad CT where
    CT fa >>= f = CT (\c -> do
        (a, c') <- fa c
        unwrap (f a) c')

instance Alternative CT where
  empty = CT (const $ Left "Unexpected error")
  CT fa <|> CT fb = CT (\c -> fa c <|> fb c)

liftC :: (Context -> Either TypeErrorBundle a) -> CT a
liftC f = CT (\c -> do 
    a <- f c
    return (a, c))

liftS :: (Context -> Context) -> CT ()
liftS f = CT (do
    c' <- f
    return (return ((), c')))

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
            S.toList $       -- for all the
            S.powerSet $     -- possible combination of
            M.argSet lin     -- (claims with) linearly qualified types
     in [(unr `M.union` comb, unr `M.union` (lin `M.difference` comb)) | comb <- lins]
     -- all possible splits that keep unrestricted channels in all contexts
     -- and distribute linear channels in the two results

member :: String -> CT Bool
member k = CT (do
    mem <- M.member k
    return . (mem,))

get :: String -> CT SpiType
get k = CT (do
    res <- M.lookup k
    case res of
        Just t -> return . (t,)
        Nothing-> Left . (("(The variable " ++ k ++ " was not found in context=") ++) . show)

replace :: String -> SpiType -> CT ()
replace k = liftS . M.insert k

update :: String -> SpiType -> CT ()
update k t = do
    found <- get k <|> CT (unwrap (pure t) <$> M.insert k t)
    guard (found == t)
    -- TODO <|>
    -- throwError

delete :: String -> CT ()
delete k = CT (return . ((),) . M.delete k)

extract :: String -> CT SpiType
extract k = do
    t <- get k
    t <$ when (unrestricted t) (delete k)

require :: (Context -> Bool) -> (Context -> TypeErrorBundle) -> CT ()
require p pp = CT (do
    g <- p
    if g
        then Right . ((),)
        else Left . pp)

unGamma :: CT ()
unGamma = require unrestricted (("Failed to type context, there are unused linear channels ctx=" ++) . show)

type Claim = (Val, SpiType)

class TypeCheck a where
    -- TODO better errors
    check :: a -> CT ()

instance TypeCheck Claim where
    check :: Claim -> CT ()
    check (Lit _, Boolean) = unGamma
    check (Var x, t) = do
        found <- get x
        guard (found == t) -- TODO <|> error
        unGamma
    check _ = empty -- TODO error


instance TypeCheck Proc where
    check :: Proc -> CT ()
    check Nil = unGamma
    check (Par p1 p2) = liftC $ do
        splits <- ndsplit
        let candidates = (\(c1, c2) -> do
                unwrap (check p1) c1
                unwrap (check p2) c2
                return ()) <$> splits
        return (choice (candidates `using` evalList rdeepseq))
        
    check (Bnd (x, Just tx) (y, Just ty) p) = do
        update x tx
        update y ty
        check p
    check (Bnd {}) = empty -- TODO error
    check (Brn g p1 p2) = CT (do
        res1 <- unwrap (check (g, Boolean)) . getUnrestricted
        res2 <- unwrap (check p1)
        res3 <- unwrap (check p2)
        (\c -> do
            res1
            res2
            res3
            return ((), c)))
    check (Rec x y p) = do
        (t, u) <- extract x >>= \case
                Qualified _ (Receiving t u) -> return (t, u)
                _ -> empty -- TODO error
        update x u
        replace y t
        check p
    check (Snd x v p) = do
        (t, u) <- extract x >>= \case
                Qualified _ (Sending t u) -> return (t, u)
                _ -> empty -- TODO error
        case (v, t) of
                (Var y, Qualified Lin _) -> do
                    t' <- extract y
                    when (t /= t') empty -- TODO error
                _ -> CT (do
                    res1 <- unwrap (check (v, t)) . getUnrestricted
                    (\c -> do
                        res1
                        return ((), c)))
        update x u
        check p
    
-- typeCheck' :: Context -> Proc -> Either TypeErrorBundle ()
-- typeCheck' ctx Nil
--     | unrestricted ctx = Right ()
--     | otherwise        = Left ("Failed to type context, there are unused linear channels ctx=" ++ show ctx)
-- typeCheck' ctx (Par p1 p2) =
--     let splits = ndsplit ctx
--         candidates = (\(ctx1, ctx2) -> do
--             typeCheck' ctx1 p1
--             typeCheck' ctx2 p2) <$> splits
--         result = candidates `using` evalList rdeepseq
--         in if any isRight result
--         then Right ()
--         else Left ("No context split could type the requested process\n" ++ show splits ++ "\n" ++ show ctx)
-- typeCheck' ctx (Bnd (x, Just tx) (y, Just ty) p) = typeCheck' (update x tx $ update y ty ctx) p
-- typeCheck' _   (Bnd {}) = Left "Bind without type annotations"
-- typeCheck' ctx (Brn g p1 p2) = do -- here we can optimize and not rely on parallelization
--     let guardCtx = getUnrestricted ctx -- the only context that could type a boolean variable is unrestricted
--     typeCheck' guardCtx (g, Boolean)
--     typeCheck' ctx p1
--     typeCheck' ctx p2
-- typeCheck' ctx (Rec x y p) = do            -- here we can optimize
--     (ctx', t, u) <- case extract x ctx of    -- if there is not, error
--             Just (c, Qualified _ (Receiving t u)) -> Right (c, t, u)
--             _                                       -> Left "Receiving channel not defined or ill-defined"
--     -- ctx types channel x
--     -- no need to check for unrestrictedness of gamma1
--     -- as gamma2 we just need to use ctx'
--     typeCheck' (M.insert y t $ update x u ctx') p
-- typeCheck' ctx (Snd x v p) = do -- similar to recceive we can optimize
--     (ctx', t, u) <- case extract x ctx of    -- if there is not, error
--             Just (c, Qualified _ (Sending t u)) -> Right (c, t, u)
--             Nothing -> Left ("Sending channel not defined"  ++ x ++ " ctx=" ++ show ctx)
--             _ -> Left ("Sending channel ill defined" ++ x ++ " ctx=" ++ show ctx)
--     ctx'' <- case (v, t) of
--             (Var y, Qualified Lin _) -> case extract y ctx' of
--                     Just (c, t') -> if t == t'
--                         then Right c
--                         else Left "Inconsistent types"
--                     Nothing -> Left "Undefined linear channel"
--             _ -> do
--                 typeCheck' (getUnrestricted ctx') (v, t)
--                 Right ctx'
--     typeCheck' (update x u ctx'') p