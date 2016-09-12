\documentclass[12pt,a4paper]{article}

%include polycode.fmt

%format <> = "\star"

%format <$> = "\mathbin{<\!\!\text{\footnotesize\$\normalsize}\!\!>}"
%format $> = "\mathbin{\text{\footnotesize\$\normalsize}\!\!>}"
%format <$ = "\mathbin{<\!\!\text{\footnotesize\$\normalsize}}"

%format <*> = "\mathbin{<\!\!\!\ast\!\!\!>}"
%format *> = "\mathbin{\ast\!\!\!>}"
%format <* = "\mathbin{<\!\!\!\ast}"

%format <|> = "\mathbin{<\!\!|\!\!>}"

%format << = "\mathbin{<\!\!\!<} "
%format >=> = "\mathbin{>\kern-0.35em=\kern-0.55em>} "
%format <=< = "\mathbin{<\kern-0.55em=\kern-0.35em<} "

\usepackage{fullpage}
\usepackage{enumerate}
\usepackage{syntax}

\grammarindent3em
\renewcommand{\grammarlabel}[2]{$#1$\hfill#2}
\renewcommand{\syntleft}{\itshape}
\renewcommand{\syntright}{}
\renewcommand{\ulitleft}{\sffamily\bfseries}
\renewcommand{\litleft}{\sffamily}
\renewcommand{\litright}{}

\newcommand{\key}[1]{\textbf{#1}}

\title{Assignment 4: Functors and Monads in Haskell}
\author{SWEN 431}
\date{Due date: November 2}

\begin{document}

\maketitle

\noindent Your task for this assignment is to implement the lambda calculus and
various extensions in Haskell using monads. Your submission should be a Literate
Haskell file compiled with \LaTeX~in the polycode format, with accompanying
explanations of your code. Examine the source of this document to find extra
formatting for some binary operators. Your submission should form a coherent
essay.

You \emph{may not} import anything defined in the \texttt{transformers} or
\texttt{mtl} packages. You must define the relevant classes and functions
yourself. When defining |Monad| instances, you must also include |Functor| and
|Applicative| instances.

\section{Implementing the Lambda Calculus (50 marks)}

Consider the following syntax for the pure, untyped lambda calculus:

\begin{center}
  \begin{minipage}{11em}
    \begin{grammar}
      <e> ::= <x> || $\lambda$<x>.<e> || <e> <e> || (<e>)
    \end{grammar}
  \end{minipage}
\end{center}

\noindent This question requires you to implement a data representation of a
lambda calculus program, and a parser and interpreter for that representation.

\subsection{The Parser}

We begin by defining a data structure and accompanying functions for parsing
simple context-free programs. The parser will not bother with lexing, and will
just produce an AST directly from text.

Note that while the parser does form a monad, we do not define it here.
\emph{You may only use the applicative functor interface} to form your parser.

\begin{code}
module Parser
  (  Parser, parse,
     parsers, parens,
     symbol, variable, keyword, number, string
  ) where

import Control.Applicative
import Data.Bifunctor
import Data.Char
import Data.Foldable
import Control.Monad
\end{code}

\noindent The parser will be fairly simple wrapper around a function that takes
the text to parse, and either fails with an error message, or produces the
result of the parse and the remaining text.

\begin{code}
newtype Parser a = Parser { runParser :: String -> Either String (a, String) }
\end{code}

\noindent This parser forms a |Functor| over its single type argument, with
|fmap| transforming the first element of the resulting pair if a parse step
succeeds.

\begin{code}
instance Functor Parser where
  fmap f = Parser . (fmap . fmap) (first f) . runParser
\end{code}

\noindent It also forms an |Applicative| functor, with |pure| maintaining the
remaining text, and the |<*>| operator running the parser from left to right,
halting on the first failure.

\begin{code}
instance Applicative Parser where
  pure a = Parser (Right . (,) a)
  f <*> a = Parser (runParser f >=> \ (g, s) -> first g <$> runParser a s)
\end{code}

\noindent We also need to be able to combine parsers such that if one fails, we
can try another one. The |Parser| type forms an |Alternative| functor that
provides this functionality.

\begin{code}
instance Alternative Parser where
  empty = Parser (const (Left "Empty parser"))
  a <|> b = Parser (\ s -> onLeft (runParser b s) (runParser a s))
    where onLeft = flip either Right . const
\end{code}

\noindent Now two parsers can be combined with the |<||>| operator, which will
use the right parser if the left one fails.

The top-level parser definition can be run by applying the string to parse to
the wrapped function, with a successful parse producing an empty string for the
remaining content.

\begin{code}
parse :: Parser a -> String -> Either String a
parse p = either Left leftovers . runParser p
  where
    leftovers (a,  "")  = Right a
    leftovers (_,  l)   = Left ("Unexpected leftovers: " ++ l)
\end{code}

Before defining our parsing operations, we'll define an auxiliary function to
construct a parser that ignores all leading whitespace and raises an exception
if it encounters the end of the input before it manages to run the given parsing
function, otherwise splitting the head and tail of the input for lookahead.

\begin{code}
parser :: ((Char, String) -> Either String (a, String)) -> Parser a
parser f = Parser (safeSplit . dropWhile isSpace >=> f)
  where
    safeSplit []       = Left "Unexpected end of input"
    safeSplit (h : t)  = Right (h, t)
\end{code}

\noindent Functions matching the input type can then be lifted into the |Parser|
type. Here's a function that consumes an identifier and returns what it
consumed:

\begin{code}
identifier :: ((Char, String) -> Either String (String, String))
identifier (h, r)
    | isAlpha h  = Right (first (h :) (span isAlphaNum r))
    | otherwise  = Left ("Expected identifier, but found " ++ show h)
\end{code}

When we use |<||>|, if both of the options fail then the resulting error will be
the one raised by the right parser, but we want an error that reports their
combination. Here's a helper that tries a list of parsers and reports a custom
error if none of them succeed.

\begin{code}
parsers :: String -> [Parser a] -> Parser a
parsers name ps = foldl' (<|>) empty ps <|> parser err
  where err (h, _) = Left ("Expected " ++ name ++ " but found " ++ show h)
\end{code}

\noindent So, to parse expressions, one can combine a series of parsers with a
call to the |parsers| function like so:

\begin{spec}
expression = parsers "an expression"
  [application, variable, function, parens expression]
\end{spec}

Now we can define some simple parsing operations to construct parsers.
The first is a function that takes a character, and produces a parser that
consumes that character, producing an error if the next character to parse is
not the one it was given.

\begin{code}
symbol :: Char -> Parser ()
symbol c = parser symbol'
  where
    symbol' (h, r)
        | c == h     = Right ((), r)
        | otherwise  = Left ("Expected " ++ show c ++ ", but found " ++ show h)
\end{code}

\noindent The second operation is a parser that will consume a variable and
return the name it consumed, making it exactly the parser form of the
|identifier| function.

\begin{code}
variable  ::  Parser String
variable  =   parser identifier
\end{code}

\noindent We can produce new operations by combining these existing ones. Here
is a function which, given a parser, produces a parser that consumes
parentheses around the given parse.

\begin{code}
parens :: Parser a -> Parser a
parens p = symbol '(' *> p <* symbol ')'
\end{code}

\noindent These definitions are all we need for now. As we extend our language
beyond the pure lambda calculus, we will add extra functions.

\subsection{Implementation}

\noindent With the parser given above, for the given syntax definition for
expression, define:

\begin{enumerate}[\hspace{2em}1)]

  \item A data structure that represents an expression (10 marks).

\begin{spec}
data Expr
\end{spec}

  \vspace{-.5em}\item A parser for an expression into your new type (20 marks).

\begin{spec}
expression :: Parser Expr
\end{spec}

  \vspace{-.5em} You are encouraged to include a syntax definition alongside
  your parser. Your concrete syntax should be simple: use the Unicode symbol for
  lambdas, and don't permit functions with more than one parameter.

  \item A function for reducing an expression to normal form (20 marks).

\begin{spec}
evaluate :: Expr -> Expr
\end{spec}

  \vspace{-.5em} You are encouraged to include reduction rules alongside your
  definitions. Don't forget to discuss which order your reduction uses, and how
  you implement substitution when applying functions.

\end{enumerate}

\noindent Add a |main| function which takes a file name to parse and run on the
command line, printing out the result of parsing and evaluating the program.
Command line arguments are accessible at |System.Environment.getArgs|.

\section{Types, Statements, and Variables (40 marks)}

Consider the following changes to the previous syntax:

\begin{center}
  \begin{minipage}{12em}
    \begin{grammar}
      <e> ::= <x> || $\lambda x:\tau$.<e> || <e> <e> || (<e>)

      <\tau> ::= <B> || $\tau\to\tau$
    \end{grammar}
  \end{minipage}
\end{center}

\noindent This question requires you to extend your existing implementation with
types, primitive values, and other extensions, using the appropriate monads. Use
the Unicode rightwards arrow symbol for function types when updating the parser.

\subsection{The Parser}

In order to handle the extensions above, we will need some more primitive
parsing operations. The first is for parsing keywords like \key{true} and
\key{false}, which is similar to parsing a variable but confirms that the
consumed identifier matches the expected name.

\begin{code}
keyword :: String -> Parser ()
keyword key = parser (identifier >=> keyword')
  where
    keyword' (name, r)
        | name == key  = Right ((), r)
        | otherwise    = Left ("Expected " ++ key ++ ", but found " ++ name)
\end{code}

\noindent Next we need to parse natural numbers, so we define a parser that
consumes all of the leading digits and turns them into a |Int|.

\begin{code}
number   ::  Parser Int
number   =   parser number'
  where
    number' (h, r)
        | isDigit h  = Right (first (read . (h :)) (span isDigit r))
        | otherwise  = Left ("Expected a number, but found " ++ show h)
\end{code}

\noindent Finally, we need to parse string literals. We'll only consider simple
strings, with no escape characters.

\begin{code}
string   ::  Parser String
string   =   parser string'
  where
    string' (h, r)
        | isQuote h  = Right (second tail (break isQuote r))
        | otherwise  = Left ("Expected a number, but found " ++ show h)
    isQuote = (== '"')
\end{code}

\noindent This provides us with all we need to begin extending the language.

\subsection{Implementation}

Implement |Reader|, |Writer|, and |State| monad transformers, and use them
appropriately to define:

\begin{enumerate}[\hspace{2em}1)]

  \item Boolean and natural numbers, along with a simple type system that has
  the base types |Bool| and |Nat| (10 marks).

  You will need to update your parser to support primitive literals and type
  annotations, and introduce some basic operations for the new primitives.

  \begin{center}
    \begin{minipage}{17em}
      \begin{grammar}
        <e> ::= \ldots || \key{true} || \key{false} || $\mathbb{N}$

        <B> ::= |Bool| || |Nat|
      \end{grammar}
    \end{minipage}
  \end{center}

  You are encouraged to include your typing rule definitions.

  \begin{spec}
type Check

data Type

check :: Expr -> Check Type
  \end{spec}

  \item Strings with the base type |String|, and the ability to handle program
  arguments using the value |argc : Nat| and the function |argv : Nat -> String|
  (10 marks).

  Your parser must also support simple string literals.

  \begin{center}
    \begin{minipage}{17em}
      \begin{grammar}
        <e> ::= \ldots || $\mathbb{S}$

        <B> ::= \ldots || |String|
      \end{grammar}
    \end{minipage}
  \end{center}

  \item The unit value with the base type |Unit|; statements separated by
  semicolons, which reduce in order and evaluate to the result of the final
  expression; and a function |print : String -> Unit| which prints to the output
  (10 marks).

  \begin{center}
    \begin{minipage}{17em}
      \begin{grammar}
        <e> ::= \ldots || |unit| || <e>; <e>

        <B> ::= \ldots || |Unit|
      \end{grammar}
    \end{minipage}
  \end{center}

  \item Mutable variables, with assignment reducing to the assigned expression
  (10 marks).

  \begin{center}
    \begin{minipage}{17em}
      \begin{grammar}
        <e> ::=
          \ldots || \key{var} $x:\tau$ = <e> \key{in} <e> || <x> = <e>
      \end{grammar}
    \end{minipage}
  \end{center}

\end{enumerate}

\noindent Note that the evaluation must still be pure (that is, not contain any
|IO|). The program arguments should be collected before evaluation, and printing
to the output should only occur after the evaluation has completed. The type of
|evaluate| should be adjusted to compensate for this.

\section{Exceptions (10 marks)}

Consider this final extension to the previous syntax:

\begin{center}
  \begin{minipage}{17em}
    \begin{grammar}
      <e> ::= \ldots || \key{throw} <e> || \key{try} <e> \key{catch} <x>.<e>
    \end{grammar}
  \end{minipage}
\end{center}

\noindent This question requires you to extend your existing implementation with
exceptions and a simple try-catch mechanism.

\subsection{Implementation}

Implement a |Result| monad transformer, and use it in combination with the
previous monads to define:

\begin{enumerate}[\hspace{2em}1)]

  \item A throw expression which uses a string as an exception, along with a
  try-catch expression to catch any exception thrown in the try body, binding
  the thrown string to an identifier in the catch body (10 marks).

\end{enumerate}

\noindent The type of |evaluate| must take into account a potential uncaught
exception.

\end{document}
