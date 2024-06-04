module SessionPi.Preprocessing where
import SessionPi.Syntax
import SessionPi.Types (Context)
import qualified Data.Map as M
import SessionPi.Abstraction
import Algebra.Lattice ((/\))
import Callstack (addCallStack)

preprocess :: Proc -> Either [String] Proc
preprocess = fillTypeHoles . liftBindings

-- bind is active in all parallel branches by definition, equivalently here we lift it to the parent node
-- inefficiente ma vabbè
liftBindings :: Proc -> Proc
liftBindings (Par p1 p2) = b1 $ b2 p'
    where
        (b1, p1') = case p1 of
                Bnd x y p -> (Bnd x y . liftBindings, p)
                _         -> (id, p1)
        (b2, p2') = case p2 of
                Bnd x y p -> (Bnd x y . liftBindings, p)
                _         -> (id, p2)
        p' = Par (liftBindings p1') (liftBindings p2')
liftBindings Nil = Nil
liftBindings (Snd x y p) = Snd x y (liftBindings p)
liftBindings (Rec x y p) = Rec x y (liftBindings p)
liftBindings (Bnd x y p) = Bnd x y (liftBindings p)
liftBindings (Brn g p1 p2) = Brn g (liftBindings p1) (liftBindings p2)

fillTypeHoles :: Proc -> Either [String] Proc
fillTypeHoles = fillTypeHoles' M.empty

-- TODO fiilTypeHoles ma con contesto astratto invece che concreto, e poi il sample viene fatto dal fondo a risalire invece che scendendo
-- perché arrivati al fondo, si ha 
fillTypeHoles' :: Context -> Proc -> Either [String] Proc
fillTypeHoles' ctx (Bnd (x, Just tx) (y, Just ty) p) = do
    let ctx' = M.insert x tx $ M.insert y ty ctx
    Bnd (x, Just tx) (y, Just ty) <$> fillTypeHoles' ctx' p

fillTypeHoles' ctx pr@(Bnd (x, _) (y, _) p) = do
    -- here both types are Nothing by construction of the program
    -- but the compiler doesn't know that
    let actx = deduce p (fmap sigma
                        $ M.delete x
                        $ M.delete y
                        ctx)
        atx' = get x actx
        aty' = get y actx
    tx <- sample (atx' /\ aDualType aty') `addCallStack` ("Error computing dual type for variable " ++ x ++ " in context " ++ show pr)
    ty <- sample (aty' /\ aDualType atx') `addCallStack` ("Error computing dual type for variable " ++ y ++ " in context " ++ show pr)
    let ctx' = M.insert x tx $ M.insert y ty ctx
    Bnd (x, Just tx) (y, Just ty) <$> fillTypeHoles' ctx' p
fillTypeHoles' _ Nil = return Nil
fillTypeHoles' ctx (Snd x y p) = Snd x y <$> fillTypeHoles' ctx p
fillTypeHoles' ctx (Rec x y p) = Rec x y <$> fillTypeHoles' ctx p

fillTypeHoles' ctx (Par p1 p2) = do
    p1' <- fillTypeHoles' ctx p1
    p2' <- fillTypeHoles' ctx p2
    return (Par p1' p2')
fillTypeHoles' ctx (Brn g p1 p2) = do
    p1' <- fillTypeHoles' ctx p1
    p2' <- fillTypeHoles' ctx p2
    return (Brn g p1' p2')