{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Index.AST
  ( Index (..),
    IndexVariableId,
    IndexContext,
    HasIndex (..),
    Constraint (..),
    IRel (..),
    emptyictx,
    fresh,
  )
where

import Data.Set (Set)
import qualified Data.Set as Set
import PrettyPrinter

type IndexVariableId = String

-- (fig. 8)
-- | The datatype of index expressions
data Index
  = IndexVariable IndexVariableId         -- Index variable         : i, j, k,...
  | Number Int                            -- Natural number         : 0,1,2,...
  | Plus Index Index                      -- Sum of indices         : i + j
  | Max Index Index                       -- Max of indices         : max(i, j)
  | Mult Index Index                      -- Product of indices     : i * j
  | Minus Index Index                     -- Natural subtraction    : i - j
  | Maximum IndexVariableId Index Index   -- Bounded maximum        :max[id < i] j
  deriving (Show, Eq)

instance Pretty Index where
  pretty (IndexVariable id) = id
  pretty (Number n) = show n
  pretty (Plus i j) = "(" ++ pretty i ++ " + " ++ pretty j ++ ")"
  pretty (Max i j) = "max(" ++ pretty i ++ ", " ++ pretty j ++ ")"
  pretty (Mult i j) = "(" ++ pretty i ++ " * " ++ pretty j ++ ")"
  pretty (Minus i j) = "(" ++ pretty i ++ " - " ++ pretty j ++ ")"
  pretty (Maximum id i j) = "max[" ++ id ++ " < " ++ pretty i ++ "] " ++ pretty j

-- Corresponds to Θ in the paper
type IndexContext = Set IndexVariableId

-- | The empty index context
emptyictx :: IndexContext
emptyictx = Set.empty

-- | The class of types that contain index variables
class HasIndex a where
  -- | @iv x@ returns the set of index variables (bound or free) that occur in @x@
  iv :: a -> Set IndexVariableId
  -- | @ifv x@ returns the set of free index variables that occur in @x@
  ifv :: a -> Set IndexVariableId
  -- | @isub i id x@ substitutes the index variable @id@ by the index @i@ in @x@
  isub :: Index -> IndexVariableId -> a -> a

-- | @wellFormed theta x@ checks if all free index variables in @x@ are in @theta@
wellFormed :: (HasIndex a) => IndexContext -> a -> Bool
wellFormed theta x = ifv x `Set.isSubsetOf` theta

instance HasIndex Index where
  iv :: Index -> Set IndexVariableId
  iv (IndexVariable id) = Set.singleton id
  iv (Number _) = Set.empty
  iv (Plus i j) = iv i `Set.union` iv j
  iv (Max i j) = iv i `Set.union` iv j
  iv (Mult i j) = iv i `Set.union` iv j
  iv (Minus i j) = iv i `Set.union` iv j
  iv (Maximum id i j) = Set.insert id (iv i `Set.union` iv j)
  ifv :: Index -> Set IndexVariableId
  ifv (IndexVariable id) = Set.singleton id
  ifv (Number _) = Set.empty
  ifv (Plus i j) = ifv i `Set.union` ifv j
  ifv (Max i j) = ifv i `Set.union` ifv j
  ifv (Mult i j) = ifv i `Set.union` ifv j
  ifv (Minus i j) = ifv i `Set.union` ifv j
  ifv (Maximum id i j) = Set.delete id (ifv i `Set.union` ifv j)
  isub :: Index -> IndexVariableId -> Index -> Index
  isub _ _ (Number n) = Number n
  isub i id j@(IndexVariable id') = if id == id' then i else j
  isub i id (Plus j k) = Plus (isub i id j) (isub i id k)
  isub i id (Max j k) = Max (isub i id j) (isub i id k)
  isub i id (Mult j k) = Mult (isub i id j) (isub i id k)
  isub i id (Minus j k) = Minus (isub i id j) (isub i id k)
  isub i id (Maximum id' j k) =
    let id'' = fresh id' [IndexVariable id, i, k]
     in Maximum id'' (isub i id j) (isub i id . isub (IndexVariable id'') id' $ k)

-- | @fresh id xs@ returns a fresh index variable name that does not occur in @xs@, @id@ if possible.
fresh :: (HasIndex a) => IndexVariableId -> [a] -> IndexVariableId
fresh id xs =
  let toavoid = Set.unions $ iv <$> xs
   in head $ filter (`Set.notMember` toavoid) $ id : [id ++ show n | n <- [0 ..]]

-- Natural lifting of well-formedness to traversable data structures
instance (Traversable t, HasIndex a) => HasIndex (t a) where
  iv :: t a -> Set IndexVariableId
  iv x = let ivets = iv <$> x in foldr Set.union Set.empty ivets
  ifv :: t a -> Set IndexVariableId
  ifv x = let ifvets = ifv <$> x in foldr Set.union Set.empty ifvets
  isub :: Index -> IndexVariableId -> t a -> t a
  isub i id x = isub i id <$> x

-- | The datatype of index relations
data IRel = Eq | Leq
  deriving (Show, Eq)

instance Pretty IRel where
  pretty Eq = "="
  pretty Leq = "≤"

-- | The datatype of index constraints
data Constraint = Constraint IRel Index Index
  deriving (Show, Eq)

instance Pretty Constraint where
  pretty (Constraint rel i j) = pretty i ++ " " ++ pretty rel ++ " " ++ pretty j
