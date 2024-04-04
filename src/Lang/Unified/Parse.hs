{-# HLINT ignore "Use <$>" #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}

module Lang.Unified.Parse
  ( parseProgram,
  )
where

import Bundle.Parse
import Data.Char
import Index.Parse
import Lang.Type.Parse
import Lang.Unified.AST
import Lang.Unified.Constant
import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Language
import Text.Parsec.String
import Text.Parsec.Token
import Control.Monad

--- PAPER LANGUAGE PARSER ---------------------------------------------------------------------------------
---
--- This module defines the parser for the unified, practical syntax of PQR.
--- This is the main parser used in the application. It is implemented using the Parsec library.
-----------------------------------------------------------------------------------------------------------

--- LEXER DEFINITION -----------------------------------------------------------------------------------

unifiedLang :: LanguageDef st
unifiedLang =
  emptyDef
    { commentLine = "--",
      commentStart = "{-",
      commentEnd = "-}",
      identStart = letter <|> char '_',
      identLetter = alphaNum <|> char '_',
      reservedNames = ["let", "in", "forall", "Circ", "apply", "fold", "lift", "box", "force", "let", "in", "[]", "()"],
      opStart = oneOf "@:\\.=!$",
      opLetter = char ':',
      reservedOpNames = ["@", "::", "!::", ":", "\\", ".", "=", "$", "->"]
    }

unifiedTokenParser :: TokenParser st
unifiedTokenParser@TokenParser
  { parens = m_parens,
    identifier = m_identifier,
    reserved = m_reserved,
    comma = m_comma,
    commaSep = m_commaSep,
    commaSep1 = m_commaSep1,
    brackets = m_brackets,
    reservedOp = m_reservedOp,
    operator = m_operator,
    whiteSpace = m_whiteSpace,
    symbol = m_symbol,
    braces = m_braces
  } = makeTokenParser unifiedLang

--- ELEMENTARY PARSERS -----------------------------------------------------------------------------------

-- parse "()" as EUnit
unitValue :: Parser Expr
unitValue =
  do
    m_reserved "()"
    return EUnit
    <?> "unit value"

-- parse "[]" as ENil
nil :: Parser Expr
nil =
  do
    m_reserved "[]"
    return $ ENil Nothing
    <?> "empty list"

-- parse a lowercase identifier as a variable
variable :: Parser Expr
variable = try $ do
  name@(first : _) <- m_identifier
  if isLower first
    then return $ EVar name
    else
      fail "Variable names must start with a lowercase letter"
        <?> "variable"

-- parse an uppercase identifier as a constant
constant :: Parser Expr
constant = try $ do
  name <- m_identifier
  case name of
    "QInit0" -> return $ EConst QInit0
    "QInit1" -> return $ EConst QInit1
    "QDiscard" -> return $ EConst QDiscard
    "Meas" -> return $ EConst Meas
    "CInit0" -> return $ EConst CInit0
    "CInit1" -> return $ EConst CInit1
    "CDiscard" -> return $ EConst CDiscard
    "Hadamard" -> return $ EConst Hadamard
    "PauliX" -> return $ EConst PauliX
    "PauliY" -> return $ EConst PauliY
    "PauliZ" -> return $ EConst PauliZ
    "CNot" -> return $ EConst CNot
    "Toffoli" -> return $ EConst Toffoli
    "MakeCRGate" -> return $ EConst MakeCRGate
    _ -> fail $ "Unrecognized constant \"" ++ name ++ "\""
    <?> "constant"

-- parse "\x :: t . e" as the (EAbs x t e)
lambda :: Parser Expr
lambda =
  do
    name <- try $ do
      m_reservedOp "\\"
      m_identifier
    m_reservedOp "::"
    typ <- parseType
    m_reservedOp "."
    e <- parseExpr
    return $ EAbs name typ e
    <?> "abstraction"

lambdaDest :: Parser Expr
lambdaDest = do
  try $ do
    m_reservedOp "\\"
    m_symbol "("
  elems <- m_commaSep1 m_identifier
  m_symbol ")"
  when (length elems < 2) $ fail "Destructuring lambda must bind at least two variables"
  m_reservedOp "::"
  typ <- parseType
  m_reservedOp "."
  e <- parseExpr
  return $ EAbs "#tmp#" typ $ EDest elems (EVar "#tmp#") e
  


-- parse "(e1, e2, ..., en)" as (EPair (EPair ... (EPair e1 e2) ... en)
-- Sugar: n-tuples are desugared left-associatively into nested pairs
tuple :: Parser Expr
tuple =
  do
    elems <- try $ do
      elems <- m_parens $ m_commaSep1 parseExpr
      when (length elems < 2) $ fail "Tuples must have at least two elements"
      return elems
    return $ ETuple elems
    <?> "tuple"

-- parse "let (x,y) = e1 in e2" as (EDest x y e1 e2)
-- Sugar: let (x0,x1,...,xn) = e1 in e2 is desugared into let (tmp,xn) = e1 in let (tmp,xn-1) = tmp in ... let (x0,x1) = tmp in e2
dest :: Parser Expr
dest =
  do
    try $ do
      m_reserved "let"
      m_symbol "("
    elems <- m_commaSep1 m_identifier
    when (length elems < 2) $ fail "Destructuring let must bind at least two variables"
    m_symbol ")"
    m_reservedOp "="
    e1 <- parseExpr
    m_reserved "in"
    e2 <- parseExpr
    return $ EDest elems e1 e2

-- parse "let x = e1 in e2" as (ELet x e1 e2)
letIn :: Parser Expr
letIn =
  do
    x <- try $ do
      m_reserved "let"
      m_identifier
    m_reservedOp "="
    e1 <- parseExpr
    m_reserved "in"
    e2 <- parseExpr
    return $ ELet x e1 e2
    <?> "let-in"

-- parse "[e1, e2, ..., en]" as (ECons e1 (ECons ... (ECons en ENil) ...))
-- Sugar: list literals are desugared right-associatively into nested Cons with Nil at the end
list :: Parser Expr
list =
  do
    elems <- m_brackets $ m_commaSep parseExpr
    return $ foldr ECons (ENil Nothing) elems
    <?> "list literal"

-- parse "let x:xs = e1 in e2" as (ELetCons x xs e1 e2)
letCons :: Parser Expr
letCons =
  do
    x <- try $ do
      m_reserved "let"
      x <- m_identifier
      m_reservedOp ":"
      return x
    xs <- m_identifier
    m_reservedOp "="
    e1 <- parseExpr
    m_reserved "in"
    e2 <- parseExpr
    return $ ELetCons x xs e1 e2
    <?> "let-cons"

-- parse "fold(e1, e2)" as (EFold e1 e2)
fold :: Parser Expr
fold =
  do
    m_reserved "fold"
    (e1, e2, e3) <- m_parens $ do
      e1 <- parseExpr
      _ <- m_comma
      e2 <- parseExpr
      _ <- m_comma
      e3 <- parseExpr
      return (e1, e2, e3)
    return $ EFold e1 e2 e3
    <?> "fold"

-- parse "apply(e1,e2)" as (EApply e1 e2)
apply :: Parser Expr
apply =
  do
    m_reserved "apply"
    (e1, e2) <- m_parens $ do
      e1 <- parseExpr
      _ <- m_comma
      e2 <- parseExpr
      return (e1, e2)
    return $ EApply e1 e2
    <?> "apply"

-- parse "@i . e" as (EIAbs i e)
iabs :: Parser Expr
iabs =
  do
    i <- try $ do
      m_reservedOp "@"
      i <- m_identifier
      m_reservedOp "."
      return i
    e <- parseExpr
    return $ EIAbs i e
    <?> "index abstraction"


--- OPERATOR PARSERS -----------------------------------------------------------------------------------

manyForceOp :: Parser (Expr -> Expr)
manyForceOp = foldr1 (.) <$> many1 forceOp
  where
    forceOp :: Parser (Expr -> Expr)
    forceOp = do
      m_reserved "force"
      return EForce

-- parse spaces as the infix operator EApp
appOp :: Parser (Expr -> Expr -> Expr)
appOp = m_whiteSpace >> return EApp <?> "application"

-- parse "$" as the infix operator EApp (lowest precedence)
dollarOp :: Parser (Expr -> Expr -> Expr)
dollarOp = m_reservedOp "$" >> return EApp <?> "application"

-- parse "!:: t" as the postfix operator (\e -> EAssume e t)
manyAssumeOp :: Parser (Expr -> Expr)
manyAssumeOp = foldr1 (.) <$> many1 assumeOp
  where
    assumeOp :: Parser (Expr -> Expr)
    assumeOp =
      do
        m_reservedOp "!::"
        t <- parseType
        return $ flip EAssume t
        <?> "type assumption"

-- parse "@ i" as the postfix operator (\e -> EIApp e i)
manyIappOp :: Parser (Expr -> Expr)
manyIappOp = foldr1 (.) <$> many1 iappOp
  where
    iappOp :: Parser (Expr -> Expr)
    iappOp =
      do
        i <- try $ do
          m_reservedOp "@"
          parseIndex
        return $ flip EIApp i
        <?> "index application"

-- parse ":" as the infix operator Cons
consOp :: Parser (Expr -> Expr -> Expr)
consOp = m_reservedOp ":" >> return ECons <?> "cons operator"

-- parse ":: t" as the postfix operator (\e -> EAnno e t)
manyAnnOp :: Parser (Expr -> Expr)
manyAnnOp = foldr1 (.) <$> many1 annOp
  where
    annOp :: Parser (Expr -> Expr)
    annOp = do
      m_reservedOp "::"
      t <- parseType
      return $ flip EAnno t
      <?> "type annotation"

-- parse "lift e" as (ELift e)
manyLiftOp :: Parser (Expr -> Expr)
manyLiftOp = foldr1 (.) <$> many1 liftOp
  where
    liftOp :: Parser (Expr -> Expr)
    liftOp = do
        m_reserved "lift"
        return ELift
        <?> "lift"

-- parse "box[bt] e" as (EBox bt e)
manyBoxOp :: Parser (Expr -> Expr)
manyBoxOp = foldr1 (.) <$> many1 boxOp
  where
    boxOp :: Parser (Expr -> Expr)
    boxOp =
      do
        m_reserved "box"
        bt <- m_brackets parseBundleType
        return $ EBox bt
        <?> "box"



--- TOP-LEVEL PARSERS -----------------------------------------------------------------------------------

delimitedExpr :: Parser Expr
delimitedExpr =
  unitValue
    <|> nil
    <|> tuple
    <|> list
    <|> m_parens parseExpr
    <|> apply
    <|> fold
    <|> constant
    <|> variable

-- parse a PQR unified expression
parseExpr :: Parser Expr
parseExpr =
  let operatorTable =
        [ [Prefix manyForceOp],
          [Prefix manyBoxOp],
          [Prefix manyLiftOp],
          [Infix appOp AssocLeft],
          [Infix consOp AssocRight],
          [Postfix manyIappOp],
          [Postfix manyAnnOp],
          [Postfix manyAssumeOp],
          [Infix dollarOp AssocRight]
        ]
      simpleExpr =
        delimitedExpr
          <|> lambda
          <|> lambdaDest
          <|> iabs
          <|> dest
          <|> letCons
          <|> letIn
   in buildExpressionParser operatorTable simpleExpr <?> "expression"

-- parse a PQR unified program
parseProgram :: Parser Expr
parseProgram =
  do
    m_whiteSpace
    e <- parseExpr
    eof
    return e
    <?> "program"