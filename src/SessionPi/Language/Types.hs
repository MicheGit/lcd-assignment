module SessionPi.Language.Types where
import SessionPi.Language

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Applicative (Alternative(empty, (<|>)))
import Control.Monad (when, unless)
import Control.Parallel.Strategies (using, evalList, rdeepseq)
import Text.Megaparsec (choice)
import Text.Printf (printf)

foldChoice :: [Either a b] -> Either [a] b
foldChoice [] = Left []
foldChoice (e:es) = case e of
    Right r -> Right r
    Left  l -> case foldChoice es of
            Right r -> Right r
            Left ls -> Left (l:ls)

mapLeft :: (a -> a') -> Either a b -> Either a' b
mapLeft f (Left l) = Left (f l)
mapLeft _ (Right r) = Right r

typeCheck :: Proc -> Either TypeErrorBundle ()
typeCheck p = fst <$> unwrap (check p) mempty

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

sideEffect :: (Context -> Context) -> CT ()
sideEffect f = CT (do
    c' <- f
    return (return ((), c')))

fromEither :: Either TypeErrorBundle a -> CT a
fromEither = liftC . const

throwError :: TypeErrorBundle -> CT a
throwError e = CT (\c -> do
    Left (printf "Error: %s\n\t within context: %s" e (show c)))

runPure :: (Context -> a) -> CT a
runPure = liftC . (return .)

ctId :: CT Context
ctId = liftC return

overrideWith :: Context -> CT ()
overrideWith = sideEffect . const

(|>) :: Context -> CT () -> CT ()
c |> ct = overrideWith c >> ct

(-<) :: CT () -> [CT ()] -> CT [Either TypeErrorBundle ()]
ct -< cts = do
    ct
    CT (\c -> do
        let d = fmap ((fst <$>) . ($ c) . unwrap) cts
        return (d, c))

(>-) :: CT [Either TypeErrorBundle ()] -> CT () -> CT ()
cts >- ct = do
    let evalIndependently = foldl (>>) (Right ()) . (`using` evalList rdeepseq)
    res <- evalIndependently <$> cts
    fromEither res >> ct

detach :: [CT ()] -> CT ()
detach cts = return () -< cts >- return ()

getUnrestricted :: Context -> Context
getUnrestricted = M.filter unrestricted

dropLinear :: CT ()
dropLinear = sideEffect getUnrestricted

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
member = runPure . M.member

get :: String -> CT SpiType
get k = do
    r <- runPure (M.lookup k)
    case r of
        Just t -> return t
        Nothing-> throwError (printf "Variable %s not defined" k)

replace :: String -> SpiType -> CT ()
replace k = sideEffect . M.insert k

update :: String -> SpiType -> CT ()
update k t = do
    may <- runPure (M.lookup k)
    case may of
        Just found -> unless (found == t) (throwError $ printf "Error updating: %s found in context with type %s which is different from %s required" k (show found) (show t))
        Nothing    -> sideEffect (M.insert k t)

delete :: String -> CT ()
delete = sideEffect . M.delete

extract :: String -> CT SpiType
extract k = do
    t <- get k
    t <$ unless (unrestricted t) (delete k)

require :: (Context -> Bool) -> TypeErrorBundle -> CT ()
require predicate e = do
    g <- runPure predicate
    unless g $ throwError e

unGamma :: CT ()
unGamma = require unrestricted "Failed to type context, there are unused linear channels"

type Claim = (Val, SpiType)

class TypeCheck a where
    -- TODO better errors
    check :: a -> CT ()

instance TypeCheck Claim where
    check :: Claim -> CT ()
    check (Lit _, Boolean) = unGamma
    check (Var x, t) = do
        found <- get x
        when (found /= t) $ throwError (printf "Error checking claim: variable %s found in context with type %s which is different from %s required" x (show found) (show t))
        unGamma
    check _ = throwError "Tryed to check a literal with a channel type"

instance TypeCheck Proc where
    check :: Proc -> CT ()
    check Nil = unGamma
    check (Par p1 p2) = do
        splits <- runPure ndsplit
        let cand c1 c2 = detach [ c1 |> check p1, c2 |> check p2 ]
        runs <- return () -< (uncurry cand <$> splits)
        let results = runs `using` evalList rdeepseq
            outcome = foldChoice results
            ppsplit = foldl (\acc split -> (printf "%s\n\t%s" acc (show split) :: String)) "No context split typed both processes. Errors were:\n"
        fromEither (mapLeft ppsplit outcome)
    check (Bnd (x, Just tx) (y, Just ty) p) = do
        update x tx
        update y ty
        check p
    check (Bnd {}) = throwError "Bind without annotations"
    check (Brn g p1 p2) = detach
        [ dropLinear >> check (g, Boolean)
        , check p1
        , check p2
        ]
    check (Rec x y p) = do
        (t, u) <- extract x >>= \case
                Qualified _ (Receiving t u) -> return (t, u)
                left -> throwError (printf "Receive channel %s typed against unmatching type: %s is not a qualified receiving pretype" x (show left))
        update x u
        replace y t
        check p
    check (Snd x v p) = do
        (t, u) <- extract x >>= \case
                Qualified _ (Sending t u) -> return (t, u)
                left -> throwError (printf "Send channel %s typed against unmatching type: %s is not a qualified sending pretype" x (show left))
        case (v, t) of
                (Var y, Qualified Lin _) -> do
                    t' <- extract y
                    when (t /= t') $ throwError (printf "Variable %s with type $s in context was typed against an unmatching type %s" x (show t) (show t'))
                _ -> detach [ dropLinear >> check (v, t) ]
        update x u
        check p
