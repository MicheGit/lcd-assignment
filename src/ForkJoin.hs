module ForkJoin where
    
import Control.Monad (foldM)


-- fork
thenFork :: (Monad m, Monad e, Functor f) => m (e a) -> f (a -> e b) -> m (f (e b))
f `thenFork` fs = do
    x <- f                   -- evaluate the first monad 
    return $ (x >>=) <$> fs  -- map the monad over the independent action(s)

-- join
-- by default the join has a behaviour of type "if even one fails, then the whole process fails"
thenJoin :: (Foldable t, Monad m, Monad e, Monoid (f a), Applicative f) => m (t (e a)) -> m (f a -> a) -> m (e a)
mf `thenJoin` f = do
    mfs <- mf -- evaluate the independent actions
    fn <- f   -- apply the second action to get the reduce function
    return (foldM                                            -- until you find an empty/error result
            (\x ->                                           -- accumulate into a single result
                fmap                                         -- if not present turn it into empty/error
                (fn . (pure x `mappend`) . pure)             -- using the specified function appended the accumulator and the result
                )
            (fn mempty)                                      -- start with the empty value
            mfs)
            

(-<) :: (Monad m, Monad e, Functor f) => m (e a) -> f (a -> e b) -> m (f (e b))
(-<) = thenFork
(>-) :: (Monad m, Foldable f, Monad e, Monoid (f a), Applicative f) => m (f (e a)) -> m (f a -> a) -> m (e a)
(>-) = thenJoin

forkJoin :: (Foldable f, Monoid (f a), Monad e, Applicative f) => f (a -> e a) -> a -> e a
forkJoin ms = return -< ms >- return