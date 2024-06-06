module Callstack where

type TypeErrorBundle a b = Either [a] b

addCallStack :: TypeErrorBundle a b -> a -> TypeErrorBundle a b
addCallStack (Left ls) l = Left (l:ls)
addCallStack r _ = r

intoCallStack ::  TypeErrorBundle l r -> TypeErrorBundle [l] r
intoCallStack (Left l) = Left [l]
intoCallStack (Right r) = Right r

fromSuccess :: (Show a) => TypeErrorBundle a b -> b
fromSuccess = \case
    { Right a -> a
    ; Left e -> error (show e)
    }

-- Folds all the eithers with Left as identity element,
--  resulting in an either with the list of all Lefts 
--  if there was no Right element, returns such Right otherwise.
foldChoice :: [TypeErrorBundle a b] -> TypeErrorBundle [a] b
foldChoice [] = Left []
foldChoice (e:es) = case e of
    Right r -> Right r
    Left  l -> case foldChoice es of
            Right r -> Right r
            Left ls -> Left (l:ls)

-- Transforms an either's Left element.
mapLeft :: ([a] -> [a']) -> TypeErrorBundle a b -> TypeErrorBundle a' b
mapLeft f (Left l) = Left (f l)
mapLeft _ (Right r) = Right r