module SessionPi.Preprocessing where

import SessionPi.Syntax ( Proc(..) )
import SessionPi.Infer
    ( Inferrable(deduce),
      AContext,
      AType(TopType, Channel, ABool, BotType),
      Abstraction(sigma),
      sample,
      aDualType,
      get,
      dualNarrow,
      lfpFrom )
import Algebra.Lattice ((/\))
import Callstack (addCallStack, TypeErrorBundle)
import qualified Data.Map as M

preprocess :: Proc -> TypeErrorBundle String Proc
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
liftBindings (Rec q x y p) = Rec q x y (liftBindings p)
liftBindings (Bnd x y p) = Bnd x y (liftBindings p)
liftBindings (Brn g p1 p2) = Brn g (liftBindings p1) (liftBindings p2)

fillTypeHoles :: Proc -> Either [String] Proc
fillTypeHoles = fillTypeHoles' M.empty

-- TODO fillTypeHoles ma con contesto astratto invece che concreto, e poi il sample viene fatto dal fondo a risalire invece che scendendo
-- perché arrivati al fondo, si ha 
fillTypeHoles' :: AContext -> Proc -> Either [String] Proc
fillTypeHoles' ctx (Bnd (x, Just tx) (y, Just ty) p) = do
    let ctx' = M.insert x (sigma tx) $ M.insert y (sigma ty) ctx
    Bnd (x, Just tx) (y, Just ty) <$> fillTypeHoles' ctx' p
fillTypeHoles' ctx pr@(Bnd (x, _) (y, _) p) = do
    -- here both types are Nothing by construction of the program
    -- but the compiler doesn't know that
    let shadow = M.delete x . M.delete y
        actx = lfpFrom (shadow ctx) (dualNarrow x y . deduce p)
    p' <- fillTypeHoles' actx p
    let actx' = deduce p' actx
        atx' = get x actx'
        aty' = get y actx'
    tx <- sample (atx' /\ aDualType aty') `addCallStack` ("Error computing dual type for variable " ++ x ++ " in context " ++ show actx ++ " for process " ++ show pr)
    ty <- sample (aty' /\ aDualType atx') `addCallStack` ("Error computing dual type for variable " ++ y ++ " in context " ++ show actx ++ " for process " ++ show pr)
    Bnd (x, Just tx) (y, Just ty) <$> fillTypeHoles' (M.insert x (sigma tx) $ M.insert y (sigma ty) ctx) p
fillTypeHoles' _ Nil = return Nil
fillTypeHoles' ctx (Snd x y p) = Snd x y <$> fillTypeHoles' ctx p
fillTypeHoles' ctx (Rec q x y p) = do
    let ety = case get x ctx of
            Channel _ _ t _ -> t
            ABool -> BotType
            BotType -> BotType
            _ -> TopType
    ty <- sample ety `addCallStack` ("Error sampling variable pass " ++ y ++ " sent by channel " ++ x ++ " from context " ++ show ctx)
    Rec q x y <$> fillTypeHoles' (M.insert y (sigma ty) ctx) p
fillTypeHoles' ctx (Par p1 p2) = do
    p1' <- fillTypeHoles' ctx p1
    p2' <- fillTypeHoles' ctx p2
    return (Par p1' p2')
fillTypeHoles' ctx (Brn g p1 p2) = do
    p1' <- fillTypeHoles' ctx p1
    p2' <- fillTypeHoles' ctx p2
    return (Brn g p1' p2')

