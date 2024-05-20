module Bisimulation where
import qualified Data.Set as S
import Data.Maybe (fromMaybe)

class (Eq a, Ord a) => Bisimulation a where
    -- A transition that represents a transformation of an object
    --  and the associated observed behaviour.
    -- In the resulting tuple, the first element is the transformed state
    --  and the second is the observed behaviour.
    -- Although the behaviour might be of any nature, here we just need 
    --  that it's in an appropriate equivalence class for the object itself.
    behave :: a -> Maybe (a, a)
    behave a = Just (a, a)

bisim :: (Bisimulation a) => S.Set (a, a) -> a -> a -> Bool
bisim _   a b | a == b = True
bisim rel a b | S.member (a, b) rel = True
bisim rel a b | S.member (b, a) rel = True
bisim rel a b = fromMaybe False $ do
    (a', oa) <- behave a
    (b', ob) <- behave b
    return (oa == ob && bisim (S.insert (a, b) rel) a' b')


(~) :: (Bisimulation a) => a -> a -> Bool
(~) = bisim S.empty

(/~) :: (Bisimulation a) => a -> a -> Bool
a /~ b = not (a ~ b)