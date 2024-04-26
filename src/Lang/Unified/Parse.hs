{-# HLINT ignore "Use <$>" #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}

module Lang.Unified.Parse
  ( parseProgram
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
import Lang.Unified.Pattern
import PrettyPrinter
import Data.List (intercalate)
import Lang.Type.AST

--- UNIFIED LANGUAGE PARSER ---------------------------------------------------------------------------------
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

--- ELEMENTARY EXPRESSION PARSERS -----------------------------------------------------------------------------------

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
  if not (isUpper first) -- accepts "_", unlike isLower
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
    "MakeNToffoli" -> return $ EConst MakeNToffoli
    "MakeNCZ" -> return $ EConst MakeNCZ
    "MakeUnitList" -> return $ EConst MakeUnitList
    _ -> fail $ "Unrecognized constant \"" ++ name ++ "\""
    <?> "constant"

-- parse "\p :: t . e" as the (EAbs p t e)
lambda :: Parser Expr
lambda =
  do
    p <- try $ do
      m_reservedOp "\\"
      parsePattern
    m_reservedOp "::"
    typ <- parseType
    m_reservedOp "."
    e <- parseExpr
    return $ EAbs p typ e
    <?> "abstraction"


-- parse "(e1, e2, ..., en)" as (ETuple [e1, e2, ..., en])
tuple :: Parser Expr
tuple =
  do
    elems <- try $ do
      elems <- m_parens $ m_commaSep1 parseExpr
      when (length elems < 2) $ fail "Tuples must have at least two elements"
      return elems
    return $ ETuple elems
    <?> "tuple"

-- parse "let p = e1 in e2" as (ELet p e1 e2)
letIn :: Parser Expr
letIn =
  do
    p <- try $ do
      m_reserved "let"
      parsePattern
    m_reservedOp "="
    e1 <- parseExpr
    m_reserved "in"
    e2 <- parseExpr
    return $ ELet p e1 e2
    <?> "let-in"

-- parse "[e1, e2, ..., en]" as (ECons e1 (ECons ... (ECons en ENil) ...))
-- Sugar: list literals are desugared right-associatively into nested Cons with Nil at the end
list :: Parser Expr
list =
  do
    elems <- m_brackets $ m_commaSep parseExpr
    return $ foldr ECons (ENil Nothing) elems
    <?> "list literal"

-- parse "fold(e1, e2, e3)" as (EFold e1 e2 e3)
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

-- parse "apply(e1, e2)" as (EApply e1 e2)
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

--- TOP-LEVEL DECLARATION PARSERS -----------------------------------------------------------------------------------

-- parse "f :: A1 -o A2 -o ... -o An -o B \n f p1 p2 ... pn = e"
-- as ELet (PVar f) (EAnno (EAbs p1 A1 (EAbs p2 A2 ... (EAbs pn An e))) (TArrow A1 (TArrow A2 ... (TArrow An B) ...))
tld :: Parser (Expr -> Expr)
tld = do
  decName <- m_identifier
  m_reservedOp "::"
  decType <- parseType
  -- endOfLine
  defName <- m_identifier
  unless (decName == defName) $ fail $ "Declaration name '" ++ decName ++ "' does not match definition name '" ++ defName ++ "'"
  args <- manyTill parsePattern (m_reservedOp "=")
  let argTypes = stripTypes decType
  unless (length args <= length argTypes) $ fail $ "Too many arguments in the definition of '" ++ defName ++ "': " ++ intercalate ", " (map pretty $ drop (length argTypes) args)
  body <- parseExpr
  -- endOfLine
  let abstractions = zipWith EAbs args argTypes
  let function = foldr ($) body abstractions
  return $ ELet (PVar defName) (EAnno function decType)
  <?> "top-level declaration"
  where stripTypes (TArrow int outt _ _) = int : stripTypes outt
        stripTypes _ = []

--- EXPRESSION OPERATOR PARSERS -----------------------------------------------------------------------------------

-- parse "force" as the prefix operator EForce, possibly applied multiple times
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

-- parse ":: t" as the postfix operator (\e -> EAnno e t), possibly applied multiple times
manyAnnOp :: Parser (Expr -> Expr)
manyAnnOp = foldr1 (.) <$> many1 annOp
  where
    annOp :: Parser (Expr -> Expr)
    annOp = do
      m_reservedOp "::"
      t <- parseType
      return $ flip EAnno t
      <?> "type annotation"

-- parse "!:: t" as the postfix operator (\e -> EAssume e t), possibly applied multiple times
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

-- parse "@ i" as the postfix operator (\e -> EIApp e i), possibly applied multiple times
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

-- parse "lift" as the prefix operator ELift, possibly applied multiple times
manyLiftOp :: Parser (Expr -> Expr)
manyLiftOp = foldr1 (.) <$> many1 liftOp
  where
    liftOp :: Parser (Expr -> Expr)
    liftOp = do
        m_reserved "lift"
        return ELift
        <?> "lift"

-- parse "box[bt]" as the prefix operator (EBox bt), possibly applied multiple times
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


--- PATTERN AND PATTERN OPERATOR PARSERS -----------------------------------------------------------------------------------

-- parse a lowercase identifier as a variable pattern
pvariable :: Parser Pattern
pvariable = try $ do
  name@(first : _) <- m_identifier
  if not (isUpper first) -- accepts "_", unlike isLower
    then return $ PVar name
    else
      fail "Variable names must start with a lowercase letter"
        <?> "variable pattern"

-- parse (p1, p2, ..., pn) as a pattern (PTuple [p1, p2, ..., pn])
ptuple :: Parser Pattern
ptuple =
  do
    elems <- try $ do
      elems <- m_parens $ m_commaSep1 parsePattern
      when (length elems < 2) $ fail "Tuple patterns must have at least two elements"
      return elems
    return $ PTuple elems
    <?> "tuple pattern"

-- parse ":" as the infix operator PCons
pconsOp :: Parser (Pattern -> Pattern -> Pattern)
pconsOp = m_reservedOp ":" >> return PCons <?> "cons operator"

--- TOP-LEVEL PARSERS -----------------------------------------------------------------------------------

-- parse a destructuring pattern
parsePattern :: Parser Pattern
parsePattern = let
  operatorTable =
    [ [Infix pconsOp AssocRight]
    ]
  simplePattern =
    pvariable
    <|> ptuple
    <|> m_parens parsePattern
  in buildExpressionParser operatorTable simplePattern <?> "pattern"
      
-- parse a PQR expression whose syntactic bounds are unambiguous
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

-- parse a PQR expression
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
          <|> iabs
          <|> letIn
   in buildExpressionParser operatorTable simpleExpr <?> "expression"

-- parse a PQR program: an expression between optional leading whitespace and EOF
parseProgram :: Parser Expr
parseProgram =
  do
    m_whiteSpace
    e <- parseExpr
    eof
    return e
    <?> "program"