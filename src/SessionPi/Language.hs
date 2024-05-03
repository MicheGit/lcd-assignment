module SessionPi.Language (Proc, Val) where

data Proc where
    Snd :: String -> Val -> Proc -> Proc
    Rec :: String -> String -> Proc -> Proc
    Par :: Proc -> Proc -> Proc
    Brn :: Val -> Proc -> Proc
    Nil :: Proc
    Bnd :: String -> String -> Proc

data Val where
    Var :: String -> Val
    Lit :: Bool -> Val

