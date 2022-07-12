module REPL where
  
import  Control.Monad           (unless)
import  Control.Comonad.Cofree  (Cofree((:<)))
import  Data.List.Unicode       ((⧺))
import  Data.Eq.Unicode         ((≡))
import  Text.Megaparsec         (errorBundlePretty)
import  System.IO               (hFlush, stdout)
import  Expr                    (prettyExpr)
import  Type                    (prettyType)
import  Parser                  (parseExpr)
import  Infer                   (infer)

repl ∷ IO ()
repl = do
  src ← prompt
  unless (src ≡ "exit") $ do 
    case parseExpr "<stdin>" src of
      Left e → putStrLn $ errorBundlePretty e
      Right a → case infer a of
        Left e → putStrLn e
        Right e@(t :< _) → putStrLn $ prettyExpr e ⧺ " : " ⧺ prettyType t
    repl
  where
    prompt = putStr "STLC> " >> hFlush stdout >> getLine