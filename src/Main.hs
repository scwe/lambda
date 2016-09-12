import Parser
import System.IO
import System.Environment
import Data.Functor
import Data.Function
import Control.Applicative

type Check = Maybe
data Expr = Var String | App Expr Expr | Func String Expr | Tru | Untrue | Nat Int deriving (Eq)

data Type = B | N

instance Show Expr where
    show (Var a) = a
    show (App a b) = "("++ show a ++ ") (" ++ show b ++ ")"
    show (Func arg body) = "\\" ++ arg ++ ". (" ++ show body ++ ")"

check :: Expr -> Check Type
check expr = undefined

var :: Parser Expr
var = fmap Var variable

func :: Parser Expr
func = Func <$> arg <*> expression
    where arg = symbol '\\' *> variable <* symbol '.'

app :: Parser Expr
app = App <$> bodyExpression <*> bodyExpression

bool :: Parser Expr
bool = (fmap (const Tru) . keyword $ "true") <|>
       (fmap (const Untrue) . keyword $ "false")

natural :: Parser Expr
natural = Nat <$> number

bodyExpression :: Parser Expr
bodyExpression = parsers "Body of an application" [var, func, parens expression]

expression :: Parser Expr
expression = parsers "An Expression" [app, bodyExpression]

substitute :: Expr -> String ->  Expr -> Expr
substitute a@(Var v1) name b = if v1 == name then b else a
substitute a@(App e1 e2) name b = App (substitute e1 name b) (substitute e2 name b)
substitute a@(Func arg body) name b | arg == name = a
                                    | otherwise = Func arg (substitute body name b)

evaluate :: Expr -> Expr
evaluate a@(App e1@(Func arg body) e2) = substitute body arg e2
evaluate a@(App e1@(App _ _) e2) = (App `on` evaluate) e1 e2
evaluate expr = expr

prettyPrint :: (Either String Expr, Either String Expr) -> IO ()
prettyPrint (a, b) = putStrLn $ show a ++ " -> " ++ show b

main :: IO ()
main = do
    args <- getArgs
    lines <- (fmap . fmap) (fmap lines . readFile) getArgs
    expressions <- fmap concat . sequence $ lines
    let results = map ((\s -> (s, fmap evaluate s)) . parse expression) expressions
    mapM_ prettyPrint results
