module InferSpec (spec) where
import Test.Hspec (Spec, describe, it, shouldSatisfy, shouldBe)
import SessionPi.Parser (parseProcess)
import SessionPi.Syntax
import SessionPi.Preprocessing
import SessionPi.Abstraction
import Data.Either (isRight, fromRight)
import qualified Data.Map as M
import Algebra.Lattice (Lattice((/\)))

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
            let z = get "_z" ctx
            z `shouldBe` Channel AnyQual ARecv TopType (Channel AnyQual ARecv TopType NonLinear)

        it "infers linear channels for a receiving tuple" $ do
            let e = parseProcess "infer test" "x2 >> (y, z) . 0 | x1 << (true, false) . 0"
            e `shouldSatisfy` isRight
            let p = liftBindings $ fromRight Nil e
                ctx = case p of
                    Bnd ("_y1", Nothing) ("_y2", Nothing) p' -> infer p'
                    _ -> M.empty
            let x1 = get "x1" ctx
            x1 `shouldBe` Channel AnyQual ASend TopType NonLinear
            let x2 = get "x2" ctx
            x2 `shouldBe` Channel AnyQual ARecv
                (Channel AnyQual ARecv TopType
                    (Channel AnyQual ARecv TopType NonLinear)) NonLinear
            let y1 = get "_y1" ctx
            y1 `shouldBe` Channel AnyQual ASend ABool (Channel AnyQual ASend ABool NonLinear)
            let y2 = get "_y2" ctx
            y2 `shouldBe` TopType
            let z = get "_z" ctx
            z `shouldBe` Channel AnyQual ARecv TopType (Channel AnyQual ARecv TopType NonLinear)

    describe "Should fill correctly dual types holes" $ do

        it "fills the unspecified types" $ do
            let e = parseProcess "infer test" "x1 >< x2 . {x2 >> (y, z) . 0 | x1 << (true, false) . 0}"
            e `shouldSatisfy` isRight
            let p = preprocess $ fromRight Nil e
                hiddenSendType = Qualified Lin (Sending Boolean (Qualified Lin (Sending Boolean End)))
                hiddenRecvType = Qualified Lin (Receiving Boolean (Qualified Lin (Receiving Boolean End)))
            p `shouldBe`
                Bnd
                    ("x1", Just (Qualified Lin (Sending hiddenSendType End)))
                    ("x2", Just (Qualified Lin (Sending hiddenRecvType End)))
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

    describe "Should compute correctly join of dual types" $ do
        it "computes binding types" $ do
            let x1 = Channel AnyQual ASend TopType NonLinear
                passedVal = Channel AnyQual ARecv TopType
                    (Channel AnyQual ARecv TopType NonLinear)
                x2 = Channel AnyQual ARecv passedVal NonLinear
            (x1 /\ aDualType x2) `shouldBe`
                Channel AnyQual ASend passedVal NonLinear


        -- it "computes binding types that are passed in parallel"
        --     let y1 = Channel AnyQual ASend ABool (Channel AnyQual ASend ABool NonLinear)
        --     let y2 = TopType
        --     let z = Channel AnyQual ARecv TopType (Channel AnyQual ARecv TopType NonLinear)



