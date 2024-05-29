module SessionPi.Preprocessing where
import SessionPi.Syntax

preprocess :: Proc -> Proc
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

fillTypeHoles = undefined
