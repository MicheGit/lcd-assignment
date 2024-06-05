module InferSpec (spec) where
import Test.Hspec (Spec, describe, it, shouldSatisfy, shouldBe)
import SessionPi.Parser (parseProcess)
import SessionPi.Syntax
import SessionPi.Preprocessing
import SessionPi.Abstraction
import Data.Either (isRight, fromRight, Either (Right))
import qualified Data.Map as M
import Algebra.Lattice (Lattice((/\)))
import Callstack (fromRight')
import SessionPi.Types (typeCheck)

spec :: Spec
spec = do

    describe "Should infer some basic types" $ do
        it "should infer a bool channel" $ do
            let e = parseProcess "infer test" "x >< y : lin?bool.end . x << z .0"
            e `shouldSatisfy` isRight
            let p = fromRight Nil e
                a = infer p
                k = get "z" a
            k `shouldBe` ABool
            let x = get "x" a
            x `shouldBe` TopType

        it "should infer a linear channel" $ do
            let e = parseProcess "infer test" "x << true . 0"
            e `shouldSatisfy` isRight
            let p = fromRight Nil e
                a = infer p
                x = get "x" a
            x `shouldBe` Channel AnyQual ASend ABool NonLinear

        it "should infer a continuos channel" $ do
            let e = parseProcess "infer test" "x << true . 0 | x << true . 0"
            e `shouldSatisfy` isRight
            let p = fromRight Nil e
                a = infer p
                x = get "x" a
            x `shouldBe` Channel OnlyUnr ASend ABool NonLinear

    describe "Should infer syntactic sugared hidden types" $ do
        it "infers linear channels for a sending tuple" $ do
            let e = parseProcess "infer test" "x << (true, false) . 0"
            e `shouldSatisfy` isRight
            let p = fromRight Nil e
                ctx = case p of
                    Bnd ("_y1", Nothing) ("_y2", Nothing) p' -> infer p'
                    _ -> M.empty
            let x = get "x" ctx
            x `shouldBe` Channel AnyQual ASend
                TopType -- TODO veramente il best I can do?
                    NonLinear
            let y1 = get "_y1" ctx
            y1 `shouldBe` Channel AnyQual ASend ABool (Channel AnyQual ASend ABool NonLinear)

        it "infers linear channels for a receiving tuple" $ do
            let e = parseProcess "infer test" "x >> (y, z) . 0"
            e `shouldSatisfy` isRight
            let p = fromRight Nil e
                ctx = infer p
            let x = get "x" ctx
            x `shouldBe` Channel AnyQual ARecv
                (Channel AnyQual ARecv TopType
                    (Channel AnyQual ARecv TopType NonLinear)) NonLinear

        it "infers hidden linear channels for a parallel compositions" $ do
            let e = parseProcess "infer test" "x2 >> (y, z) . 0 | x1 << (true, false) . 0"
            e `shouldSatisfy` isRight
            let p = liftBindings $ fromRight Nil e
                ctx = case p of
                    Bnd ("_y1", Nothing) ("_y2", Nothing) p' -> infer p'
                    _ -> M.empty
            let x1 = get "x1" ctx
            x1 `shouldBe` Channel AnyQual ASend TopType NonLinear
            let x2 = get "x2" ctx
                passedVal = Channel AnyQual ARecv TopType
                    (Channel AnyQual ARecv TopType NonLinear)
            x2 `shouldBe` Channel AnyQual ARecv passedVal NonLinear
            let y1 = get "_y1" ctx
            y1 `shouldBe` Channel AnyQual ASend ABool (Channel AnyQual ASend ABool NonLinear)
            let y2 = get "_y2" ctx
            y2 `shouldBe` TopType

        it "parses the some apparently unrelated types" $ do
            let p = Par
                        (Rec "x2" "_z"
                            (Rec "_z" "y"
                                (Rec "_z" "z" Nil)))
                        (Snd "x1" (Var "_y2")
                            (Snd "_y1" (Lit True)
                                (Snd "_y1" (Lit False) Nil)))
                ac = infer p
                ty1 = get "_y1" ac
            ty1 `shouldBe` Channel AnyQual ASend ABool (Channel AnyQual ASend ABool NonLinear)
            let tx1 = get "x1" ac
                tx2 = get "x2" ac
            tx1 `shouldBe` Channel AnyQual ASend TopType NonLinear
            tx2 `shouldBe` Channel AnyQual ARecv
                (Channel AnyQual ARecv TopType (Channel AnyQual ARecv TopType NonLinear))
                    NonLinear

        it "parses some related types" $ do
            let p = Bnd ("_y1", Nothing) ("_y2", Nothing) (Par
                        (Rec "x2" "_z"
                            (Rec "_z" "y"
                                (Rec "_z" "z" Nil)))
                        (Snd "x1" (Var "_y2")
                            (Snd "_y1" (Lit True)
                                (Snd "_y1" (Lit False) Nil))))
                ac = infer p
                tzs = Channel AnyQual ARecv ABool (Channel AnyQual ARecv ABool NonLinear)
                tzr = Channel AnyQual ARecv TopType (Channel AnyQual ARecv TopType NonLinear)
            let tx1 = get "x1" ac
                tx2 = get "x2" ac
            tx1 `shouldBe` Channel AnyQual ASend tzs NonLinear
            tx2 `shouldBe` Channel AnyQual ARecv tzr NonLinear

        it "parses the some tight related types" $ do
            let p = Par
                        (Rec "x2" "_z"
                            (Rec "_z" "y"
                                (Rec "_z" "z" Nil)))
                        (Snd "x1" (Var "_y2")
                            (Snd "_y1" (Lit True)
                                (Snd "_y1" (Lit False) Nil)))
                tz = Channel AnyQual ARecv ABool (Channel AnyQual ARecv ABool AEnd)
                ac = deduce p (M.fromList
                    [ ("x1", Channel AnyQual ASend tz AEnd)
                    , ("x2", Channel AnyQual ASend tz AEnd)])
                ty1 = get "_y1" ac
                ty2 = get "_y2" ac
            ty1 `shouldBe` Channel AnyQual ASend ABool (Channel AnyQual ASend ABool NonLinear)
            ty2 `shouldBe` Channel AnyQual ARecv ABool (Channel AnyQual ARecv ABool AEnd)
            ty2 /\ aDualType ty1 `shouldBe` ty2
            -- let tx1 = get "x1" ac
            --     tx2 = get "x2" ac
            -- tx1 `shouldBe` Channel AnyQual ASend TopType NonLinear
            -- tx2 `shouldBe` Channel AnyQual ARecv tz NonLinear



    describe "Should fill correctly dual types holes" $ do

        it "fills the unspecified types" $ do
            let e = parseProcess "infer test" "x1 >< x2 . x2 >> (y, z) . 0 | x1 << (true, false) . 0"
            e `shouldSatisfy` isRight
            let p = fromRight' $ preprocess $ fromRight Nil e
                hiddenSendType = Qualified Lin (Sending Boolean (Qualified Lin (Sending Boolean End)))
                hiddenRecvType = Qualified Lin (Receiving Boolean (Qualified Lin (Receiving Boolean End)))
            p `shouldBe`
                Bnd
                    ("x1", Just (Qualified Lin (Sending   hiddenRecvType End)))
                    ("x2", Just (Qualified Lin (Receiving hiddenRecvType End)))
                    (Bnd
                        ("_y1", Just hiddenSendType)
                        ("_y2", Just hiddenRecvType)
                        (Par
                            (Rec "x2" "_z"
                                (Rec "_z" "y"
                                    (Rec "_z" "z" Nil)))
                            (Snd "x1" (Var "_y2")
                                (Snd "_y1" (Lit True)
                                    (Snd "_y1" (Lit False) Nil)))))

        -- it "preserves precision of inferred types" $ do
        --     let e = parseProcess "infer test" " x2 >> (y, z) . 0 | x1 << (true, false) . 0"
        --     e `shouldSatisfy` isRight
        --     let p = liftBindings $ fromRight' e
        --     let actx = infer p
        --         atx = get "x1" actx
        --         aty = get "x2" actx
        --         actx' = M.insert "x1" (atx /\ aDualType aty) $ M.insert "x2" (aty /\ aDualType atx) actx
        --         e' = fillTypeHoles' actx' p
        --     e' `shouldSatisfy` isRight
        --     let p' = fromRight' e'
        --         shadowed = M.delete "x1" $ M.delete "x2" actx'
        --     -- p' `shouldBe` p
        --     shadowed `shouldBe` M.empty
        --     -- p' `shouldBe` p
        --     let actx'' = deduce p' shadowed
        --         atx' = get "x1" actx''
        --         aty' = get "x2" actx''
        --     (atx' /\ aDualType aty') `shouldBe` Channel AnyQual ASend (Channel AnyQual ARecv ABool (Channel AnyQual ARecv ABool AEnd)) NonLinear
        --     (aty' /\ aDualType atx') `shouldBe` Channel AnyQual ARecv (Channel AnyQual ARecv ABool (Channel AnyQual ARecv ABool AEnd)) NonLinear

        it "doesn't narrow precision of subsequent receives" $ do
            let e = parseProcess "infer test" " x2 >> (y, z) . 0"
            e `shouldSatisfy` isRight
            let p = fromRight' e
            let actx = lfpFrom M.empty (dualNarrow "x1" "x2" . deduce p)
                tx2 = get "x2" actx
            tx2 `shouldBe` Channel AnyQual ARecv (Channel AnyQual ARecv TopType (Channel AnyQual ARecv TopType NonLinear)) NonLinear

        it "doesn't narrow precision of subsequent receives even with parallelzation" $ do
            let e = parseProcess "infer test" " x2 >> (y, z) . 0 | x1 << (true, false) . 0"
            e `shouldSatisfy` isRight
            let p = fromRight' e
            let actx = lfpFrom M.empty (dualNarrow "x1" "x2" . deduce p)
                tx2 = get "x2" actx
                tx1 = get "x1" actx
            (tx2 /\ aDualType tx1) `shouldBe` Channel AnyQual ARecv (Channel AnyQual ARecv ABool (Channel AnyQual ARecv ABool NonLinear)) NonLinear

        it "infers correctly all channels types" $ do
            let pro = fromRight' $ fillTypeHoles' (M.singleton "v" ABool) (Bnd ("p1", Nothing) ("p2", Nothing) (Snd "p1" (Var "v") Nil))
                tp2 = case pro of
                    (Bnd _ ("p2", Just t) _) -> t
                    _ -> End
            tp2 `shouldBe` Qualified Lin (Receiving Boolean End)

        it "infer correctly complex channels types" $ do
            let p = Bnd ("p2",Nothing) ("p1",Nothing)
                        (Bnd ("_y1",Nothing) ("_y2",Nothing)
                            (Bnd ("x1", Nothing) ("x2", Nothing)
                                (Bnd ("c", Nothing) ("d", Nothing)
                                    (Par
                                    (Rec "p1" "_z"
                                        (Rec "_z" "j"
                                            (Rec "_z" "w"
                                                (Snd "j" (Lit True)
                                                    (Snd "j" (Lit True)
                                                        (Snd "w" (Var "j") Nil)
                                                            )))))
                                    (Snd "p2" (Var "_y2")
                                        (Snd "_y1" (Var "c")
                                            (Snd "_y1" (Var "x1")
                                                (Rec "d" "b1"
                                                    (Rec "d" "b2"
                                                        (Rec "x2" "z"
                                                            (Rec "z" "y" Nil)
                                                                ))))))
                                    ))))
                pro = fromRight' $ preprocess p
                (tp2, tp1) = case pro of
                    (Bnd ("p2", Just t2) ("p1", Just t1) _) -> (t2, t1)
                    _ -> (End, Boolean)
            tp1 `shouldBe` dualType tp2

        it "fills subprocess and then infers the right missing channels" $ do
            let sp = Par
                        (Rec "p1" "_z"
                            (Rec "_z" "j"
                                (Rec "_z" "w"
                                    (Snd "j" (Lit True)
                                        (Snd "j" (Lit True)
                                            (Snd "w" (Var "j") Nil)
                                                )))))
                        (Snd "p2" (Var "_y2")
                            (Snd "_y1" (Var "c")
                                (Snd "_y1" (Var "x1")
                                    (Rec "d" "b1"
                                        (Rec "d" "b2"
                                            (Rec "x2" "z"
                                                (Par
                                                    (Rec "z" "y" Nil)
                                                    (Snd "d" (Lit True) Nil))
                                                    ))))))
                ctx = lfpFrom M.empty (deduce sp)
                tx1 = get "_y1" ctx
                tx2 = get "_y2" ctx
            aDualType (aDualType tx2 /\ tx1) `shouldBe` tx2 /\ aDualType tx1

        it "infers the right missing channels through fixpoint iteration" $ do
            -- p2 >< p1 . x1 >< x2. c >< d.
            let p = liftBindings $ fromRight' $ parseProcess "test" "x1 >< x2. c >< d.{p1 >> (j, w) . j << true . j << true . w << j.0} | p2 << (c, x1) . d >> b1 . d >> b2. x2 >> z . z >> y .0"
                ctx = lfpFrom M.empty (dualNarrow "p1" "p2" . deduce p)
                tx1 = get "p1" ctx
                tx2 = get "p2" ctx
            aDualType (aDualType tx2 /\ tx1) `shouldBe` tx2 /\ aDualType tx1
            -- ctx `shouldBe` M.empty

        it "infers correctly from send" $ do
            let p = liftBindings $ fromRight' $ parseProcess "test" "w << j . 0"
                ctx = deduce p (M.fromList
                    [ ("w", Channel AnyQual ASend (Channel AnyQual ARecv TopType NonLinear) NonLinear)
                    , ("j", Channel AnyQual ARecv ABool NonLinear)
                    ])
                tw = get "w" ctx
            tw `shouldBe` Channel AnyQual ASend (Channel AnyQual ARecv ABool NonLinear) NonLinear

        it "infers correctly from multiple send" $ do
            let p = Par
                        (Rec "p1" "_z"
                            (Rec "_z" "j"
                                (Rec "_z" "w"
                                    (Snd "j" (Lit True)
                                        (Snd "j" (Lit True)
                                            (Snd "w" (Var "j") Nil)
                                                )))))
                        (Snd "p2" (Var "_y2")
                            (Snd "_y1" (Var "c")
                                (Snd "_y1" (Var "x1")
                                    (Rec "d" "b1"
                                        (Rec "d" "b2"
                                            (Rec "x2" "z"
                                                (Par
                                                    (Rec "z" "y" Nil)
                                                    (Snd "d" (Lit True) Nil))
                                                    ))))))

                tjend = Channel AnyQual ARecv ABool NonLinear
                tjstart = Channel AnyQual ASend ABool (Channel AnyQual ASend ABool tjend)
                ctx = dualNarrow "x1" "x2" $ lfpFrom (M.fromList
                    [ ("c", tjstart)
                    , ("d", aDualType tjstart)
                    ])
                    (dualNarrow "p1" "p2" . deduce p)
                tx1 = get "x1" ctx
                twexpect = Channel AnyQual ASend tjend NonLinear
            tx1 `shouldBe` twexpect




    describe "Should compute correctly join of dual types" $ do
        it "computes binding types" $ do
            let x1 = Channel AnyQual ASend TopType NonLinear
                passedVal = Channel AnyQual ARecv TopType
                    (Channel AnyQual ARecv TopType NonLinear)
                x2 = Channel AnyQual ARecv passedVal NonLinear
            (x1 /\ aDualType x2) `shouldBe`
                Channel AnyQual ASend passedVal NonLinear

        it "computes binding between similar types" $ do
            let y1 = Channel AnyQual ASend ABool (Channel AnyQual ASend ABool NonLinear)
                y2 = Channel AnyQual ARecv TopType (Channel AnyQual ARecv TopType NonLinear)
            (y2 /\ aDualType y1) `shouldBe`
                Channel AnyQual ARecv ABool (Channel AnyQual ARecv ABool NonLinear)

        it "computes join between tight types" $ do
            let t1 = Channel AnyQual ASend (Channel AnyQual ARecv ABool (Channel AnyQual ARecv ABool NonLinear)) NonLinear
                t2 = Channel AnyQual ARecv (Channel AnyQual ARecv TopType (Channel AnyQual ARecv TopType NonLinear)) NonLinear
            t1 /\ aDualType t2 `shouldBe` t1

        it "synthetizes types from abstractions" $ do
            let concrete = Qualified Lin
                    (Sending (Qualified Lin (Receiving Boolean (Qualified Lin (Receiving Boolean End)))) End)
                abstract = Channel AnyQual ASend (Channel AnyQual ARecv ABool (Channel AnyQual ARecv ABool AEnd)) NonLinear
            concrete `shouldBe` fromRight' (sample abstract)




