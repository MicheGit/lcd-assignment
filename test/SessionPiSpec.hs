module SessionPiSpec (spec) where
import Test.Hspec

import SessionPi.Parser
import SessionPi.Language

import Text.Megaparsec (parse)
import Data.Either (isLeft)

spec :: Spec
spec = do
    specLeaves
    specExpr

specLeaves :: Spec
specLeaves = do
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
    
    describe "Should parse channel binds" $ do
        it "parses a bind " $ do
            let expected = Right (Bnd "x" "y" Nil)
            let result = parse bind "test" "x >< y . 0 . end"
            result `shouldBe` expected

        it "parses a composed bind and if" $ do
            let expected = Right (Bnd "x" "falsey" (Brn (Var "x") Nil Nil))
            let result = parse bind "test" "x >< falsey.if x then 0 else 0"
            result `shouldBe` expected
    
    describe "Should parse receive actions" $ do
        it "parses a receive" $ do
            let expected = Right (Rec "x" "y" Nil)
            let result = parse receive "test" "x >> y .0"
            result `shouldBe` expected

        it "refuses a receive on a value" $ do
            let result = parse receive "test" "x >> true .0"
            result `shouldSatisfy` isLeft
        
        it "refuses a receive from a value" $ do
            let result = parse receive "test" "false >> false .0"
            result `shouldSatisfy` isLeft
        
    describe "Should parse send actions" $ do
        it "parses a send" $ do
            let expected = Right (Snd "x" (Lit True) Nil)
            let result = parse send "test" "x << true.0"
            result `shouldBe` expected
        
        it "refuses a send on a value" $ do
            let result = parse send "test" "true << true.0"
            result `shouldSatisfy` isLeft
            



specExpr :: Spec
specExpr = do
    describe "Should parse pipes" $ do
        it "parses an inactive pipe" $ do
            let expected = Right (Par Nil Nil)
            let result = parse processExpr "test" "0 | 0"
            result `shouldBe` expected
    
        it "parses a complex pipe" $ do
            let result = parse processExpr "test" "{x >< y .0} | if true then 0 | 0 else 0"
            let expected = Right (Par (Bnd "x" "y" Nil) (Brn (Lit True) (Par Nil Nil) Nil))
            result `shouldBe` expected
    
    describe "Should parse composed propcesses" $ do
        it "parses a simple process" $ do
            let result = parse process "test" "x >< y . x << true . 0"
            let expected = Right (Bnd "x" "y" (Snd "x" (Lit True) Nil))
            result `shouldBe` expected


        it "parses two communicating processes" $ do
            let result = parse process "test" "x >< y . {x << true . 0} | y >> g . if g then 0 else 0"
            let expected = Right (Bnd "x" "y" (Par (Snd "x" (Lit True) Nil) (Rec "y" "g" (Brn (Var "g") Nil Nil))))
            result `shouldBe` expected

        
