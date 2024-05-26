module SessionPi.Abstraction where
import Algebra.Lattice (Lattice ((\/), (/\)), BoundedMeetSemiLattice (top), BoundedJoinSemiLattice (bottom), BoundedLattice)
import qualified Data.Map as M
import SessionPi.Syntax (Claim, SpiType (..), Qualifier (..), Pretype (..), thenProcess, argument, Proc (..), Val (..), BoundVar)
import Data.Maybe (fromMaybe)

class (BoundedLattice (AbstractDomain c)) => Abstraction c where
    type AbstractDomain c
    -- abstract semantics
    sigma :: c -> AbstractDomain c

data AQual where
    TopQual :: AQual
    AUn :: AQual
    ALin :: AQual
    BotQual :: AQual
    deriving (Eq, Show)

instance Lattice AQual where
    (\/) :: AQual -> AQual -> AQual
    a \/ b       | a == b = a
    TopQual \/ _ = TopQual
    BotQual \/ a = a
    _ \/ TopQual = TopQual
    a \/ BotQual = a
    _ \/ _       = TopQual

    (/\) :: AQual -> AQual -> AQual
    a /\ b       | a == b = a
    TopQual /\ a = a
    BotQual /\ _ = BotQual
    a /\ TopQual = a
    _ /\ BotQual = BotQual
    _ /\ _       = BotQual

instance BoundedMeetSemiLattice AQual where
    top :: AQual
    top = TopQual

instance BoundedJoinSemiLattice AQual where
    bottom :: AQual
    bottom = BotQual

instance Abstraction Qualifier where
    type AbstractDomain Qualifier = AQual
    sigma :: Qualifier -> AbstractDomain Qualifier
    sigma Un  = AUn
    sigma Lin = ALin

data AAct where
    TopAct :: AAct
    ASend :: AAct
    ARecv :: AAct
    BotAct :: AAct
    deriving (Eq, Show)

instance Lattice AAct where
    (\/) :: AAct -> AAct -> AAct
    a \/ b      | a == b = a
    TopAct \/ _ = TopAct
    BotAct \/ a = a
    _ \/ TopAct = TopAct
    a \/ BotAct = a
    _ \/ _      = TopAct

    (/\) :: AAct -> AAct -> AAct
    a /\ b      | a == b = a
    TopAct /\ a = a
    BotAct /\ _ = BotAct
    a /\ TopAct = a
    _ /\ BotAct = BotAct
    _ /\ _      = BotAct

instance BoundedMeetSemiLattice AAct where
    top :: AAct
    top = TopAct

instance BoundedJoinSemiLattice AAct where
    bottom :: AAct
    bottom = BotAct

instance Abstraction Pretype where
    type AbstractDomain Pretype = AAct
    sigma :: Pretype -> AbstractDomain Pretype
    sigma (Sending _ _)   = ASend
    sigma (Receiving _ _) = ARecv

data AType where
    TopType :: AType
    ABool :: AType
    AProc :: AType
    AEnd :: AType
    Channel :: AQual -> AAct -> AType -> AType -> AType
    BotType :: AType
    deriving (Eq, Show)

instance Lattice AType where
    (\/) :: AType -> AType -> AType
    a \/ b       | a == b = a
    TopType \/ _ = TopType
    BotType \/ a = a
    _ \/ TopType = TopType
    a \/ BotType = a
    ABool \/ _   = TopType
    _ \/ ABool   = TopType
    (Channel q1 a1 v1 p1) \/ (Channel q2 a2 v2 p2) = Channel (q1 \/ q2) (a1 \/ a2) (v1 \/ v2) (p1 \/ p2)
    _ \/ _       = AProc

    (/\) :: AType -> AType -> AType
    a /\ b       | a == b = a
    TopType /\ a = a
    BotType /\ _ = BotType
    a /\ TopType = a
    _ /\ BotType = BotType
    ABool /\ _   = BotType
    _ /\ ABool   = BotType
    (Channel q1 a1 v1 p1) /\ (Channel q2 a2 v2 p2) = Channel (q1 /\ q2) (a1 /\ a2) (v1 /\ v2) (p1 /\ p2)
    AProc /\ p   = p
    p /\ AProc   = p
    _ /\ _       = BotType

instance BoundedMeetSemiLattice AType where
    top :: AType
    top = TopType

instance BoundedJoinSemiLattice AType where
    bottom :: AType
    bottom = BotType

instance Abstraction Val where
    type AbstractDomain Val = AType
    sigma :: Val -> AType
    sigma (Lit _) = ABool
    sigma (Var _) = TopType

instance Abstraction SpiType where
    type AbstractDomain SpiType = AType
    sigma :: SpiType -> AbstractDomain SpiType
    sigma End     = AEnd
    sigma Boolean = ABool
    sigma (Qualified q pretype) = Channel (sigma q) (sigma pretype) (sigma v) (sigma p)
        where
            v = argument pretype
            p = thenProcess pretype
    sigma (TypeVar _) = TopType -- TODO
    sigma (Recursive _ _) = TopType -- TODO

type AContext = M.Map String AType

instance Lattice AContext where
    (\/) :: AContext -> AContext -> AContext
    (\/) = M.unionWith (\/)
    (/\) :: AContext -> AContext -> AContext
    (/\) = M.intersectionWith (/\)

merge :: [AContext] -> AContext
merge = foldl (M.unionWith (/\)) M.empty

class Inferrable a where
    infer :: a -> AContext

instance Inferrable Claim where
    infer :: Claim -> AContext
    infer (Lit _, _) = M.empty -- from literal claims we infer nothing
    infer (Var x, t) = M.singleton x (sigma t)

instance Inferrable BoundVar where
    infer :: BoundVar -> AContext
    infer (x, m) = M.singleton x (maybe TopType sigma m)

instance Inferrable Proc where
    infer :: Proc -> AContext
    infer Nil = M.empty -- from empty set we infer nothing
    infer (Brn g p1 p2) =
        let iguard = infer (g, Boolean)
            i1     = infer p1
            i2     = infer p2
         in merge [iguard, i1, i2]
    infer (Snd x v p) =
        let i = infer p
            pthen = fromMaybe AEnd (M.lookup x i)
         in M.insert x (Channel ALin ASend (sigma v) pthen) i
    infer (Rec x y p) =
        let i = infer p
            pthen = fromMaybe AEnd (M.lookup x i)
            ay    = fromMaybe AEnd (M.lookup y i)
         in M.insert x (Channel ALin ARecv ay pthen) i
    infer (Bnd (x1, _) (x2, _) p) = M.delete x1 $ M.delete x2 $ infer p
    -- we infer that before that this bind, (at least those bindings of) x1 and x2 are not used
    infer (Par p1 p2) =
        let i1 = infer p1
            i2 = infer p2
         in M.unionWith parMeet i1 i2 -- TODO e se invece fosse solo \/

parMeet :: AType -> AType -> AType
parMeet = undefined




