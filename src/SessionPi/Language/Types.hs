module SessionPi.Language.Types where
import SessionPi.Language

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad (when, unless)
import Control.Parallel.Strategies (using, evalList, rdeepseq)
import Text.Printf (printf)

-- We want to typecheck processes and claims over both values and variables
type Claim = (Val, SpiType)

-- Contexts are maps of claims on variables
type Context = M.Map String SpiType

type TypeErrorBundle = String

-- Type checking is modeled with context transition
-- A context transition represents a condition that the context must satisfy
--  and yelds a result (when needed) and a new context to check against new 
--  requirements.
-- Context transitions are monads (as well as applicatives and functors), 
--  so they can be chained together.
newtype CT a = CT {unwrap :: Context -> Either TypeErrorBundle (a, Context)}

-- A rule of the type \Gamma |- a
--  where a = Proc | Claim
class TypeCheck a where
    check :: a -> CT ()

-- Example: Un(\Gamma) represents the condition for which the context has only
--  unrestricted claims, i.e. there are no unused linear channels.
unGamma :: CT ()
unGamma = require unrestricted "Failed to type context, there are unused linear channels"

-- The require function lifts boolean predicates over contexts to CTs.
-- This function generalize all requirements over subsequent checking.
require :: (Context -> Bool) -> TypeErrorBundle -> CT ()
require predicate e = do
    g <- liftPure predicate
    unless g $ throwError e

-- The throwError function throws the error argument and appends the context
--  that raised that error.
throwError :: TypeErrorBundle -> CT a
throwError e = CT (\c -> do
    Left (printf "Error: %s\n\t within context: %s" e (show c)))

-- Lifts a pure function to a context transition.
liftPure :: (Context -> a) -> CT a
liftPure = liftC . (return .)

instance TypeCheck Claim where
    check :: Claim -> CT ()
    check (Lit _, Boolean) = unGamma
    check (Var x, t) = do
        found <- get x
        when (found /= t) $ throwError (printf "Error checking claim: variable %s found in context with type %s which is different from %s required" x (show found) (show t))
        unGamma
    check _ = throwError "Tryed to check a literal with a channel type"


-- The liftC function lifts an Either predicate over contexts to a CT
--  which is pure with regards to the context, i.e. it doesn't change
--  the input context
liftC :: (Context -> Either TypeErrorBundle a) -> CT a
liftC f = CT (\c -> do
    a <- f c
    return (a, c))

-- The liftEither function maps an Either object to a rule that always 
--  ends up in that either without changing the context.
liftEither :: Either TypeErrorBundle a -> CT a
liftEither = liftC . const

-- Returns a context transition that does a side effect on the input 
--  context as described by the argument.
sideEffect :: (Context -> Context) -> CT ()
sideEffect f = CT (do
    c' <- f
    return (return ((), c')))

-- Returns a context that ignores the previous context and restarts
--  with a new one.
overrideWith :: Context -> CT ()
overrideWith = sideEffect . const

-- Returns the current context as a result.
ctId :: CT Context
ctId = liftC return

-- The `start` operator describes a computation that starts with a 
--  context unrelated with the preceding ones.
(|>) :: Context -> CT () -> CT ()
c |> ct = overrideWith c >> ct

-- The `fork` operator describes a context transition that needs 
--  more premises. It describes which premises are to be checked.
(-<) :: CT () -> [CT ()] -> CT [Either TypeErrorBundle ()]
ct -< cts = do
    ct
    CT (\c -> do
        let d = fmap ((fst <$>) . ($ c) . unwrap) cts
        return (d, c))

-- The `join` operator combines the different premises 
--  into one single thread of execution, requiring all premises
--  to be truthy.
(>-) :: CT [Either TypeErrorBundle ()] -> CT () -> CT ()
cts >- ct = do
    let evalIndependently = foldl (>>) (Right ()) . (`using` evalList rdeepseq)
    res <- evalIndependently <$> cts
    liftEither res >> ct

-- Simply run in parallel different premises with the given context unchanged.
detach :: [CT ()] -> CT ()
detach cts = return () -< cts >- return ()

instance TypeCheck Proc where
    check :: Proc -> CT ()
    check Nil = unGamma
    check (Par p1 p2) = do
        splits <- liftPure ndsplit
        let cand c1 c2 = detach [ c1 |> check p1, c2 |> check p2 ]
        runs <- return () -< (uncurry cand <$> splits)
        let results = runs `using` evalList rdeepseq
            outcome = foldChoice results
            ppsplit = foldl (\acc split -> (printf "%s\n\t%s" acc (show split) :: String)) "No context split typed both processes. Errors were:\n"
        liftEither (mapLeft ppsplit outcome)
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

typeCheck :: Proc -> Either TypeErrorBundle ()
typeCheck p = fst <$> unwrap (check p) M.empty

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
member = liftPure . M.member

get :: String -> CT SpiType
get k = do
    r <- liftPure (M.lookup k)
    case r of
        Just t -> return t
        Nothing-> throwError (printf "Variable %s not defined" k)

replace :: String -> SpiType -> CT ()
replace k = sideEffect . M.insert k

update :: String -> SpiType -> CT ()
update k t = do
    may <- liftPure (M.lookup k)
    case may of
        Just found -> unless (found == t) (throwError $ printf "Error updating: %s found in context with type %s which is different from %s required" k (show found) (show t))
        Nothing    -> sideEffect (M.insert k t)

delete :: String -> CT ()
delete = sideEffect . M.delete

extract :: String -> CT SpiType
extract k = do
    t <- get k
    t <$ unless (unrestricted t) (delete k)


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

