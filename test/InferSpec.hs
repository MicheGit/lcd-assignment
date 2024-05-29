module InferSpec (spec) where
import Test.Hspec (Spec, describe, it, shouldSatisfy, shouldBe)
import SessionPi.Parser (parseProcess)
import Data.Either (isRight, fromRight)
import SessionPi.Syntax (Proc(Nil, Bnd), preprocess)
import SessionPi.Abstraction (get, AType (ABool, Channel, AEnd, TopType, NonLinear), infer, AQual (AnyQual, OnlyUnr), AAct (ASend, ARecv))
import qualified Data.Map as M

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
            let p = preprocess $ fromRight Nil e
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



            