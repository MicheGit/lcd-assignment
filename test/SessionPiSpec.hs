module SessionPiSpec (spec) where
import Test.Hspec

import SessionPi.Parser
import SessionPi.Language

import Text.Megaparsec (parse)
import Data.Either (isLeft)



spec :: Spec
spec = do
    describe "Should parse literals" $ do
        it "parses true" $ do
            let result = parse literal "test" "true  "
            result `shouldBe` Right True

        it "parses false" $ do
            let result = parse literal "test" "false"
            result `shouldBe` Right False

        it "fails to parse falsey" $ do
            let result = parse literal "test" "falsey"
            result `shouldSatisfy` isLeft

    describe "Should parse variables" $ do
        it "parses x" $ do
            let result = parse variable "test" "x <<"
            result `shouldBe` Right "x"

        it "fails to parse a keyword" $ do
            let result = parse variable "test" "true"
            result `shouldSatisfy` isLeft

        it "parses falsey which is similar to a keyword" $ do
            let result = parse variable "test" "falsey"
            result `shouldBe` Right "falsey"

    describe "Should parse values" $ do
        it "parses the variable x" $ do
            let result = parse value "test" "x dd"
            let expected = Right (Var "x")
            result `shouldBe` expected

        it "parses the literal false" $ do
            let result = parse value "test" "false >> dd"
            let expected = Right (Lit False)
            result `shouldBe` expected

        it "parses the variable falsey" $ do
            let result = parse value "test" "falsey dd"
            let expected = Right (Var "falsey")
            result `shouldBe` expected

    describe "Should parse inactions" $ do
        it "parses successfully an inaction" $ do
            let result = parse inaction "test" "0 else 0"
            result `shouldBe` Right Nil

    describe "Should parse branches" $ do
        it "parses a literal branch" $ do
            let expected = Right (Brn (Lit True) Nil Nil)
            let result = parse branch "test" "if true then 0 else 0"
            result `shouldBe` expected

        it "parses a variable branch" $ do
            let expected = Right (Brn (Var "falsey") Nil Nil)
            let result = parse branch "test" "if falsey then 0 else 0"
            result `shouldBe` expected

        it "parses a nested then branch" $ do
            let expected = Right (Brn (Var "falsey") (Brn (Var "falsey") Nil Nil) Nil)
            let result = parse branch "test" "if falsey then if falsey then 0 else 0 else 0"
            result `shouldBe` expected
        
        it "parses a nested else branch" $ do
            let expected = Right (Brn (Var "falsey") Nil (Brn (Var "falsey") Nil Nil))
            let result = parse branch "test" "if falsey then 0 else if falsey then 0 else 0"
            result `shouldBe` expected
        

        it "parses a nested curly then branch" $ do
            let expected = Right (Brn (Var "falsey") (Brn (Var "falsey") Nil Nil) Nil)
            let result = parse branch "test" "if falsey then {if falsey then 0 else 0 }else 0"
            result `shouldBe` expected
