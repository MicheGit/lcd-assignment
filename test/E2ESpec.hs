module E2ESpec (spec) where
import Test.Hspec (Spec, describe, it, shouldSatisfy, shouldBe)
import SessionPi.Parser (parseProcess)
import SessionPi.Types (typeCheck, TypeErrorBundle)
import SessionPi.Preprocessing (preprocess)
import Data.Either ( isLeft )

fromRight' :: (Show a) => Either a b -> b
fromRight' = \case 
    { Right a -> a
    ; Left e -> error (show e)
    }

loadInfer :: String -> Either TypeErrorBundle ()
loadInfer = fromRight' . fmap (\p -> do
    e <- preprocess p
    typeCheck e) . parseProcess "test"

spec :: Spec
spec = do
    describe "Should refuse malformed processes as defined in chapter 3" $ do
        it "refuses x1 >< x2 . x1 << true . 0 | x2 >> y . y << false . 0" $ do
            let check = loadInfer "x1 >< x2 . x1 << true . 0 | x2 >> y . y << false . 0"
            check `shouldSatisfy` isLeft
        
        it "refuses x1 >< x2 . if x1 then 0 else 0" $ do
            let check = loadInfer "x1 >< x2 . if x1 then 0 else 0"
            check `shouldSatisfy` isLeft
        
        it "refuses x >< x . x << true .0 | x >> y . 0" $ do
            let check = loadInfer "x >< x . x << true .0 | x >> y . 0"
            check `shouldSatisfy` isLeft
        
        it "refuses x1 >< x2: lin?bool.end . x1 << true . 0 | x2 >> y . y << false . 0" $ do
            let check = loadInfer "x1 >< x2: lin?bool.end . x1 << true . 0 | x2 >> y . y << false . 0"
            check `shouldSatisfy` isLeft
        
        it "refuses x1 >< x2: end . if x1 then 0 else 0" $ do
            let check = loadInfer "x1 >< x2: end . if x1 then 0 else 0"
            check `shouldSatisfy` isLeft
        
        it "refuses x >< x: lin?bool.end . x << true .0 | x >> y . 0" $ do
            let check = loadInfer "x >< x: lin?bool.end . x << true .0 | x >> y . 0"
            check `shouldSatisfy` isLeft

        it "refuses two linears processes sending instances" $ do
            let check = loadInfer "x1 >< x2: lin?bool.end . x1 << true.0 | x1 << false.0 | x2 >> y .0"
            check `shouldSatisfy` isLeft
        
        it "accepts three unrestricted processes sending instances" $ do
            let check = loadInfer "x1 >< x2: rec x.?bool.x . x1 << true.0 | x1 << false.0 | x1 << true.0"
            check `shouldBe` Right ()

        it "accepts duality simple send/receive" $ do
            let check = loadInfer "x1 >< x2: lin?bool.end . x1 << true .0 | x2 >> z .0"
            check `shouldBe` Right ()
        
        it "accepts duality composed send/receive" $ do
            let check = loadInfer "c1 >< c2: lin?bool.lin!bool.end . c1 << true . c1 >> w . 0 | c2 >> z . c2 << false.0"
            check `shouldBe` Right ()

        it "accepts duality uncompliant channels" $ do
            let check = loadInfer "x1 >< x2 . x1 << true .0 | x2 << false .0"
            check `shouldSatisfy` isLeft
        
        it "refuses duality uncompliant processes" $ do
            let check = loadInfer "c1 >< c2 . c1 << true . c1 >> w . 0 | c2 >> z . c2 >> t.0"
            check `shouldSatisfy` isLeft
 

