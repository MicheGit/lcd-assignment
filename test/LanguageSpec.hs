module LanguageSpec (spec) where
import Test.Hspec (Spec, describe, it)
import SessionPi.Language
import Bisimulation

spec :: Spec
spec = do
    specEquiv

specEquiv :: Spec
specEquiv = do
    describe "Simple types should be equal" $ do
        it "Compares Boolean with Boolean" $ do
            Boolean ~ Boolean

        it "Compares Boolean with End" $ do
            End /~ Boolean

        it "Compares two variables" $ do
            TypeVar "x" ~ TypeVar "x"

    describe "Qualified types should be equal" $ do
        it "Compares lin?bool.end to lin?bool.end" $ do
            Qualified Lin (Sending Boolean End) ~ Qualified Lin (Sending Boolean End)
        
        it "Compares lin?bool.end to un?bool.end" $ do
            Qualified Lin (Sending Boolean End) /= Qualified Un (Sending Boolean End)
        
    describe "Recursive types should be equal" $ do
        it "Compares two recursive types, not needing an unfold" $ do
            Recursive "x" (Qualified Un (Sending Boolean (TypeVar "x")))
                ~ Recursive "x" (Qualified Un (Sending Boolean (TypeVar "x")))
        
        it "Compares two recursive types, needing a substitution" $ do
            Recursive "x" (Qualified Un (Sending Boolean (TypeVar "x")))
                ~ Recursive "y" (Qualified Un (Sending Boolean (TypeVar "y")))

        it "Compares two recursive types, needing unfold" $ do
            Recursive "x" (Qualified Un (Sending Boolean (TypeVar "x")))
                ~ Qualified Un (Sending Boolean (Recursive "x" (Qualified Un (Sending Boolean (TypeVar "x")))))

        it "Compares two non-simple recursive types" $ do
            Recursive "x" (
                Qualified Un (Sending Boolean (Qualified Un (Receiving Boolean (TypeVar "x"))))
                ) ~ 
                Qualified Un (Sending Boolean (Recursive "y" (
                                                Qualified Un (Receiving Boolean (Qualified Un (Sending Boolean (TypeVar "y"))))
                                                )))

        it "Compares two different recursive types" $ do
            Recursive "x" (Qualified Un (Sending Boolean (Qualified Un (Receiving Boolean (TypeVar "x")))))
                /~ Qualified Un (Sending Boolean (Recursive "y" (Qualified Un (Receiving Boolean (Qualified Lin (Sending Boolean (TypeVar "y")))))))

            

