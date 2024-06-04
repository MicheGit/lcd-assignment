module Callstack where

addCallStack :: Either [l] r -> l -> Either [l] r
addCallStack (Left ls) l = Left (l:ls)
addCallStack r _ = r

intoCallStack :: Either l r -> Either [l] r
intoCallStack (Left l) = Left [l]
intoCallStack (Right r) = Right r

fromRight' :: (Show a) => Either a b -> b
fromRight' = \case
    { Right a -> a
    ; Left e -> error (show e)
    }