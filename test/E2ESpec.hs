module E2ESpec (spec) where
import Test.Hspec (Spec, describe, it, shouldSatisfy, shouldBe)
import SessionPi.Parser (parseProcess)
import SessionPi.Types (typeCheck, TypeErrorBundle, TypeCheck (check), CT (unwrap))
import SessionPi.Preprocessing (preprocess)
import Data.Either ( isLeft, isRight )
import qualified SessionPi.Types as T
import qualified Data.Map as M
import SessionPi.Syntax (SpiType(Recursive, Qualified, Boolean, End, TypeVar), Qualifier (Un, Lin), Pretype (Sending, Receiving), Proc(..), Val(..))
import Data.List (intercalate)
import Callstack (fromRight')

composeErrorBundle :: Either [String] Proc -> Either String ()
composeErrorBundle = \case
    { Left es -> Left (intercalate "\n\t-" es)
    ; Right r -> typeCheck r
    }

loadInfer :: String -> Either TypeErrorBundle ()
loadInfer = fromRight' . fmap (composeErrorBundle . preprocess) . parseProcess "test"

spec :: Spec
spec = do
    describe "Should be compliant to the examples in section 3" $ do
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

        it "refuses something that would be accepted if the duality was applied to passed values too" $ do
            let check = loadInfer "x1 >< x2 . y1 >< y2 . x1 << y2 .0 | x2 >> z . z << true .0 | y1 << false.0"
            check `shouldSatisfy` isLeft

        it "accepts a well-typed deadlock" $ do
            let check = loadInfer "x1 >< x2 . y1 >< y2 . x1 << true . y1 << false .0 | y2 >> x . x2 >> w .0"
            check `shouldSatisfy` isRight

    describe "Should be compliant to the examples in section 4" $ do

        it "accepts a loop typed variable" $ do
            let process = fromRight' $ parseProcess "test" "x2 >> z . z << true.0 | x2 >> w . w << false.0"
                check = T.unwrap (T.check process) (M.singleton "x2" (Recursive "x"
                    (Qualified Un (Receiving (Qualified Lin (Sending Boolean End)) (TypeVar "x")))))
            check `shouldSatisfy` isRight

        it "accepts tuple passing processes with type hint linear" $ do
            let parsed = fromRight' $ parseProcess "test" "p2 >< p1 . x1 >< x2: lin? (lin? bool.end).end. c >< d. {p1 >> (j, w) . j << true . j << true . w << j.0} | p2 << (c, x1) . d >> b1 . d >> b2. x2 >> z . {d << true .0 | z >> y .0}"
                pro = fromRight' $ preprocess parsed
            let check = typeCheck pro
            check `shouldSatisfy` isRight

        it "accepts tuple passing processes with type hint" $ do
            let parsed = fromRight' $ parseProcess "test" "p2 >< p1 . x1 >< x2: lin? (rec x.? bool.end).end. c >< d. {p1 >> (j, w) . j << true . j << true . w << j.0} | p2 << (c, x1) . d >> b1 . d >> b2. x2 >> z . z >> y .0"
                pro = fromRight' $ preprocess parsed
            let check = typeCheck pro
            check `shouldSatisfy` isRight

        it "accepts tuple passing processes" $ do
            -- let expected = Bnd ("p2",Nothing) ("p1",Nothing) 
            --             (Bnd ("_y1",Nothing) ("_y2",Nothing) 
            --                 (Bnd ("x1", Nothing) ("x2", Nothing) 
            --                     (Bnd ("c", Nothing) ("d", Nothing) 
            --                         (Par 
            --                         (Rec "p1" "_z" 
            --                             (Rec "_z" "j" 
            --                                 (Rec "_z" "w" 
            --                                     (Snd "j" (Lit True) 
            --                                         (Snd "j" (Lit True) 
            --                                             (Snd "w" (Var "j") Nil)
            --                                                 ))))) 
            --                         (Snd "p2" (Var "_y2") 
            --                             (Snd "_y1" (Var "c") 
            --                                 (Snd "_y1" (Var "x1") 
            --                                     (Rec "d" "b1" 
            --                                         (Rec "d" "b2" 
            --                                             (Rec "x2" "z" 
            --                                                 (Rec "z" "y" Nil)
            --                                                     ))))))
            --                         ))))
            let parsed = fromRight' $ parseProcess "test" "p2 >< p1 . x1 >< x2. c >< d. {p1 >> (j, w) . j << true . j << true . w << j.0} | p2 << (c, x1) . d >> b1 . d >> b2. x2 >> z . {d << true .0 | z >> y .0}"
                pro = fromRight' $ preprocess parsed
            -- pro `shouldBe` Nil
            let check = typeCheck pro
            check `shouldSatisfy` isRight

        it "accepts linear channel becoming unrestricted" $ do
            let check = loadInfer "x1 >< x2: lin?bool.rec x . !bool.x . x1 <<true . {x1 >> y . 0 | x1 >> z .0} | x2 >> x . {x2 << true .0 |x2 << false .0 |x2 << true .0 }"
            check `shouldSatisfy` isRight

        it "accpets linear channel becoming unrestricted 2" $ do
            let check = loadInfer "x1 >< x2: lin?bool.rec x.!end.x. x1 << true .x1 >> y.x1 >> y.0 | x2 >> z.0"
            check `shouldSatisfy` isRight

        it "refuses linear channel used more than once" $ do
            let check = loadInfer "x1 >< x2: lin?bool.rec x.!bool.x . x1 << true . y1 >> y .0 | x2 >> y . x2 << true.0 | x2 >> w.x2 << true.0"
            check `shouldSatisfy` isLeft

        it "accepts tuple sending two ending of a channel" $ do
            let check = loadInfer "a1 >< a2 . a2 >> (y1, y2) . {y1 << false .0 | y2 >> z .0} | x1 >< x2 . a1 << (x1, x2) . 0"
            check `shouldSatisfy` isRight

    describe "Should be compliant to examples in section 5" $ do
        it "refuses replication of nested linear channels" $ do
            let parsed = preprocess $ fromRight' $ parseProcess "test" "un x2 >> z . c << true .0 | x1 << true.0 | x1 << true.0 "
            parsed `shouldSatisfy` isRight
            let tx2 = Recursive "x" (Qualified Un (Receiving Boolean (TypeVar "x")))
                tx1 = Recursive "x" (Qualified Un (Sending Boolean (TypeVar "x")))
                chk = unwrap (check $ fromRight' parsed) $ M.fromList
                    [ ("x2", tx2)
                    , ("x1", tx1)
                    , ("c", Qualified Lin (Sending Boolean End))
                    ]
            chk `shouldSatisfy` isLeft

        it "accepts replication when passing channel instead" $ do
            let parsed = preprocess $ fromRight' $ parseProcess "test" "un x2 >> z . z << true .0 "
            parsed `shouldSatisfy` isRight
            let chk = unwrap (check $ fromRight' parsed) $ M.singleton "x2" (Recursive "x" (Qualified Un (Receiving (Qualified Lin (Sending Boolean End)) (TypeVar "x"))))
            chk `shouldSatisfy` isRight
