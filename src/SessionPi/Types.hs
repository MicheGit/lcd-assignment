module SessionPi.Types where

import SessionPi.Syntax
    ( Restrictable(predicate),
      SpiType(Qualified, Boolean),
      Pretype(Sending, Receiving),
      Qualifier(..),
      Val(..),
      Proc(..) )

import Callstack (foldChoice, mapLeft, TypeErrorBundle)
import Bisimulation ((~), Bisimulation (behave))

import Control.Applicative (Alternative (empty, (<|>)))
import Control.Monad (when, unless, forM_)
import Control.Parallel.Strategies (using, rdeepseq, parList)
import Text.Printf (printf)

import qualified Data.Map as M
import qualified Data.Set as S
import Data.Functor ((<&>))


type Claim = (Val, SpiType)

-- Contexts are maps of claims on variables
type Context = M.Map String SpiType

-- Drops any linear claim in the context
getUnrestricted :: Context -> Context
getUnrestricted = M.filter (predicate Un)

-- Computes all possible distribution of linear variables in the context,
--  i.e. it computes all possible splits of the "linear subset" of the context
--  preserving all unrestricted variables
ndsplit :: Context -> [(Context, Context)]
ndsplit ctx | M.size ctx == 0 = [(mempty, mempty)]
ndsplit ctx =
    let unr = getUnrestricted ctx
        lin = M.difference ctx unr
        lins :: [Context]
        lins =
            (M.fromArgSet <$>) $
            S.toList $       -- for all the       -- for all the       -- for all the       -- for all the
                   -- for all the
            S.powerSet $     -- possible combination of     -- possible combination of     -- possible combination of
            M.argSet lin     -- (claims with) linearly qualified types
     in [(unr `M.union` comb, unr `M.union` (lin `M.difference` comb)) | comb <- lins]
     -- all possible splits that keep unrestricted channels in all contexts
     -- and distribute linear channels in the two results

type TypeError = Char

-- Type checking is modeled with context transition
-- A context transition represents a condition that the context must satisfy
--  and yelds a result (when needed) and a new context to check against new 
--  requirements.
-- Context transitions are monads (as well as applicatives and functors), 
--  so they can be chained together.
newtype CT a = CT {unwrap :: Context -> TypeErrorBundle TypeError (a, Context)}

-- A rule of the type \Gamma |- a
--  where a = Proc | Claim
class NDTypeCheck a where
    ndcheck :: a -> CT ()

-- Example: Un(\Gamma) represents the condition for which the context has only
--  unrestricted claims, i.e. there are no unused linear channels.
gammaPred :: Qualifier -> CT ()
gammaPred q = require (predicate q) "Failed to type context, there are unused linear channels"

-- The require function lifts boolean predicates over contexts to CTs.
-- This function generalize all requirements over subsequent checking.
require :: (Context -> Bool) -> String -> CT ()
require predicate e = do
    g <- liftPure predicate
    unless g $ throwError e

-- The throwError function throws the error argument and appends the context
--  that raised that error.
throwError :: String -> CT a
throwError e = CT (\c -> do
    Left (printf "Error: %s\n\t within context: %s" e (show c)))

-- Lifts a pure function to a context transition.
liftPure :: (Context -> a) -> CT a
liftPure = liftC . (return .)

instance NDTypeCheck Claim where
    ndcheck :: Claim -> CT ()
    -- Any literal value types boolean iff the context is unrestricted
    ndcheck (Lit _, Boolean) = gammaPred Un
    -- Any variable types the type t iff an equivalent claim is present in the context (and the other claims are unrestricted)
    ndcheck (Var x, t) = do
        found <- get x
        when (found /= t) $ throwError (printf "Error checking claim: variable %s found in context with type %s which is different from %s required" x (show found) (show t))
        gammaPred Un
    -- Any other ndcheck yields an error
    ndcheck c = throwError (printf "Tried to ndcheck %s, i.e. a literal with a channel type" (show c))


-- The liftC function lifts an Either predicate over contexts to a CT
--  which is pure with regards to the context, i.e. it doesn't change
--  the input context
liftC :: (Context -> TypeErrorBundle TypeError a) -> CT a
liftC f = CT (\c -> do
    a <- f c
    return (a, c))

-- The liftEither function maps an Either object to a rule that always 
--  ends up in that either without changing the context.
liftEither :: TypeErrorBundle TypeError a -> CT a
liftEither = liftC . const

-- Returns a context transition that does a side effect on the input 
--  context as described by the argument.
sideEffect :: (Context -> Context) -> CT ()
sideEffect f = CT (do
    c' <- f
    return (return ((), c')))

deleteSet :: S.Set String -> Context -> Context
deleteSet s = foldl (.) id (M.delete <$> S.toList s)

contextDiff :: S.Set String -> CT ()
contextDiff s = forM_ s (\x -> do
    t <- liftPure (M.lookup x)
    if predicate Un t
        then delete x
        else throwError "Context difference used with linear variable.")

-- Returns the current context as a result.
ctId :: CT Context
ctId = liftC return

-- The `start` operator describes a computation that starts with a 
--  context unrelated with the preceding ones.
(|>) :: Context -> CT () -> CT ()
c |> ct = sideEffect (const c) >> ct

-- Context manipulation following the Data.Map interface

-- Pure evaluation of whether a variable is defined
member :: String -> CT Bool
member = liftPure . M.member

-- Get the type of a variable. It yields an error if the variable
--  is not defined.
get :: String -> CT SpiType
get k = do
    r <- liftPure (M.lookup k)
    case r of
        Just t -> return t
        Nothing-> throwError (printf "Variable %s not defined" k)

-- Overrides a variable claim in the context
override :: String -> SpiType -> CT ()
override k = sideEffect . M.insert k

-- Updates a variable claim following the context update rules:
--  - if the context didn't have a claim on the same variable, behave as insert
--  - throw an error unless the updating type was unrestricted and bisimilar to the found type
update :: String -> SpiType -> CT ()
update k t = do
    may <- liftPure (M.lookup k)
    case may of
        Just found -> unless (predicate Un t && found ~ t) (throwError $ printf "Error updating: %s found in context with type %s which is different from %s required" k (show found) (show t))
        Nothing    -> sideEffect (M.insert k t)

-- Removes a variable claim from the context
delete :: String -> CT ()
delete = sideEffect . M.delete

-- Gets a variable claim and removes it unless it was unrestricted
extract :: String -> CT SpiType
extract k = do
    t <- get k
    t <$ unless (predicate Un t) (delete k)

-- Drops any linear claim in the context
dropLinear :: CT ()
dropLinear = sideEffect getUnrestricted

-- The `fork` operator describes a sequent that needs 
--  more premises. It describes which premises are to be checked.
(-<) :: CT () -> [CT ()] -> CT [TypeErrorBundle TypeError ()]
ct -< cts = do
    ct
    CT (\c -> do
        let d = fmap ((fst <$>) . ($ c) . unwrap) cts
        return (d, c))

-- The `join` operator combines the different premises 
--  into one single thread of execution, requiring all premises
--  to be truthy. The premises are evaluated in parallel by default.
(>-) :: CT [TypeErrorBundle TypeError ()] -> CT () -> CT ()
cts >- ct = do
    let allRight = foldl (>>) (Right ()) -- . (`using` parList rdeepseq)
    res <- allRight <$> cts
    liftEither res >> ct
infix 0 >-

-- Simply run in parallel different premises with the given context unchanged.
detach :: [CT ()] -> CT ()
detach cts = return () -< cts >- return ()


instance NDTypeCheck Proc where
    ndcheck :: Proc -> CT ()
    -- The inaction process is well typed when the context has no linear variables
    ndcheck Nil = gammaPred Un
    -- The parallel process is whell typed when there exist two context splits typing the parallel
    -- Note that it requires only one split to be successful, as not in the default multiple-premises behaviour.
    ndcheck (Par p1 p2) = do
        splits <- liftPure ndsplit
        runs <- return () -< (candidate <$> splits)
        let results = runs `using` parList rdeepseq
            outcome = foldChoice results
            -- ppsplit = foldl (\acc split -> (printf "%s\n\t%s" acc (show split) :: String)) "No context split typed both processes. Errors were:\n"
        liftEither (mapLeft (const "No context split typed both processes.") outcome)
        where
            candidate (c1, c2) = (return () -< [ c1 |> ndcheck p1, c2 |> ndcheck p2 ] <&> (`using` parList rdeepseq)) >- return ()
    -- A bind is well typed iff the subprocess is well typed overriding the definitions of the bounded variables.
    ndcheck (Bnd (x, Just tx) (y, Just ty) p) = do
        override x tx
        override y ty
        ndcheck p
    ndcheck (Bnd {}) = throwError "Bind without type definitions untypable - type inference not implemented."
    -- A branch is well typed iff:
    --  - the guard is a boolean
    --  - both the "then" and "else" processes are well typed under the same context
    -- Note that this is a semplification justified by the fact that in no way the ndcheck of a
    --  boolean variable or literal "consumes" a linear claim.
    -- Hence all the linear claims are preserved through any split of the context.
    ndcheck (Brn g p1 p2) = detach
        [ dropLinear >> ndcheck (g, Boolean)
        , ndcheck p1
        , ndcheck p2
        ]
    -- A receiving process is well typed iff the receiving channel is defined and its type is a qualified
    --  receiving pretype; furthermore it needs to update the channel's type and override the newly bound variable
    --  before type checking the subprocess.
    ndcheck (Rec q1 x y p) = do
        gammaPred q1 <|> throwError "Failed to type process: there are linear channels in replicated environment"
        t <- extract x
        (v, u) <- case behave t of
            Just (u, Qualified q2 (Receiving v _)) -> do
                when (q1 == Un && q2 /= Un) $ throwError (printf "Failed to type replicating channel %s against linear type %s" x (show t))
                return (v, u)
            b -> throwError (printf "Channel %s : %s does not behave like a receiving channel, but rather as %s" x (show t) (show b))
        update x u
        override y v
        ndcheck p
    -- A sending process is well typed iff the sending channel's type is a qualified sending pretype,
    --  and then the context has to:
    --  - type the value to send
    --  - type the remaining subprocess
    -- If the value to send was to NDTypeCheck against an unrestricted type, then it is sufficient that
    --  the unrestricted subcontext types such claim.
    -- Otherwise, it is sufficient to find (and removing) a matching claim in the context.
    ndcheck (Snd x v p) = do
        t <- extract x
        (a, u) <- case behave t of
            Just (u, Qualified _ (Sending a _)) -> return (a, u)
            b -> throwError (printf "Channel %s : %s does not behave like a sending channel, but rather as %s" x (show t) (show b))
        case (v, a) of
                (Var y, Qualified Lin _) -> do
                    a' <- extract y
                    when (a /= a') $ throwError (printf "Variable %s with type %s in context was typed against an unmatching type %s" x (show t) (show a'))
                _ -> detach [ dropLinear >> ndcheck (v, a) ]
        update x u
        ndcheck p

-- To ndcheck whether a process is well typed it is sufficient to ndcheck it against the empty context.
ndtypeCheck :: Proc -> TypeErrorBundle TypeError ()
ndtypeCheck p = fst <$> unwrap (ndcheck p) M.empty


class TypeCheck a where
    type Output a
    check :: a -> CT (Output a)

instance TypeCheck Claim where
    type Output Claim = ()
    check :: Claim -> CT ()
    check (Lit _, Boolean) = return ()
    check (Var x, t@(Qualified Lin _)) = do
        found <- extract x
        when (found /= t) $ throwError (printf "Error checking claim: variable %s found in context with type %s which is different from %s required" x (show found) (show t))
    check (Var x, t) = do
        found <- get x
        when (found /= t) $ throwError (printf "Error checking claim: variable %s found in context with type %s which is different from %s required" x (show found) (show t))
    check c = throwError (printf "Tried to check %s, i.e. a literal with a channel type" (show c))

foldRight :: [Either a b] -> Either a [b]
foldRight [] = Right []
foldRight (x:xs) = case x of 
    Left l -> Left l
    Right r -> case foldRight xs of
        Left l -> Left l
        Right rs -> Right (r:rs)

evalIndependently :: [CT a] -> CT [(a, Context)]
evalIndependently [] = return []
evalIndependently cts = CT (\ctx -> do
    let runs = ($ ctx) . unwrap <$> cts
    results <- foldRight runs
    return (results, ctx))

allEqual :: Eq a => [a] -> Bool
allEqual [] = True
allEqual xs = foldl (\acc a -> acc && a == hd) True xs
    where
        hd = head xs


instance TypeCheck Proc where
    type Output Proc = S.Set String
    check :: Proc -> CT (S.Set String)
    check Nil = return S.empty
    check (Par p1 p2) = do
        l <- check p1
        contextDiff l -- removes all used channels
        check p2
    check (Brn g p1 p2) = do
        check (g, Boolean)
        ls <- evalIndependently
            [ check p1
            , check p2
            ]
        unless (allEqual ls) $ throwError (printf "Both branches of statements must yield the same results: %s \\= %s while checking %s" (show $ head ls) (show $ ls !! 1) (show $ Par p1 p2))
        sideEffect $ const $ snd $ head ls
        return (fst $ head ls)
    check (Snd x v p) = do
        qtu <- extract x
        (u, q, t) <- case behave qtu of
            Just (u, Qualified q (Sending t _)) -> return (u, q, t)
            b -> throwError (printf "Channel %s : %s does not behave like a sending channel, but rather as %s" x (show qtu) (show b))
        check (v, t)
        update x u
        l <- check p
        if q == Lin
            then return (S.insert x l)
            else return l
    check (Rec q1 x y p) = do
        qtu <- extract x
        (u, q2, t) <- case behave qtu of
            Just (u, Qualified q2 (Receiving t _)) -> return (u, q2, t)
            b -> throwError (printf "Channel %s : %s does not behave like a receiving channel, but rather as %s" x (show qtu) (show b))
        override y t
        update x u
        l <- check p
        -- when (q1 == Un && (l /= S.empty)) $ throwError (printf "There should be no linear variable in suprocess %s since it is included in a replicated environment" (show p)) 
        contextDiff $ S.singleton y
        let l' = S.delete y l
        -- TODO c'è un errore nel paper?
        when (q1 == Un && (l' /= S.empty)) $ throwError (printf "There should be no linear variable in suprocess %s since it is included in a replicated environment" (show p)) 
        return (if q2 == Lin
            then S.insert x l'
            else l')
    check (Bnd (x, Just tx) (y, Just ty) p) = do
        override x tx
        override y ty
        l <- check p
        contextDiff $ S.fromList [x, y]
        return (S.delete x $ S.delete y l)
    check (Bnd {}) = throwError "Bind without type definitions untypable - type inference not implemented."

typeCheck :: Proc -> TypeErrorBundle TypeError ()  
typeCheck p = fst <$> unwrap doCheck M.empty
    where
        doCheck :: CT ()
        doCheck = do
            _ <- check p
            gammaPred Un

-- Utilities

-- Functor Applicative Monad instances of context transitions
instance Functor CT where
    fmap :: (a -> b) -> CT a -> CT b
    fmap f (CT fa) = CT (\c -> do
        (a, c') <- fa c
        return (f a, c'))

instance Applicative CT where
    pure :: a -> CT a
    pure x = CT (\c -> Right (x, c))
    (<*>) :: CT (a -> b) -> CT a -> CT b
    CT fn <*> CT fa = CT (\c -> do
        (f, c')  <- fn c
        (a, c'') <- fa c'
        return (f a, c''))

instance Monad CT where
    (>>=) :: CT a -> (a -> CT b) -> CT b
    CT fa >>= f = CT (\c -> do
        (a, c') <- fa c
        unwrap (f a) c')

instance Alternative CT where
    empty :: CT a
    empty = throwError "Undefined error"
    (<|>) :: CT a -> CT a -> CT a
    CT f1 <|> CT f2 = CT (\c -> case f1 c of
            Right r -> Right r
            Left _ -> f2 c) 


