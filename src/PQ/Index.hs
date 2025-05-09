{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module PQ.Index
  ( Index (..),
    IVarId,
    IndexContext,
    emptyictx,
  )
where

import Circuit
import qualified Data.HashSet as Set
import PrettyPrinter
import Panic (undesugaredPanic)

type IVarId = String

-- | The datatype of index expressions
data Index
  = IVar IVarId                           -- Index variable         : i, j, k,...
  | Number Int                            -- Natural number         : 0,1,2,...
  | Plus Index Index                      -- Sum of indices         : i + j
  | Max Index Index                       -- Max of indices         : max(i, j)
  | Mult Index Index                      -- Product of indices     : i * j
  | Minus Index Index                     -- Natural subtraction    : i - j
  | BoundedMax IVarId Index Index         -- Bounded maximum        : max[id < i] j
  | BoundedMin IVarId Index Index         -- Bounded minimum        : min[id < i] j
  | BoundedSum IVarId Index Index         -- Bounded sum            : sum[id < i] j
  -- Abstract resource operators 
  | Output QuantumOperation Int [Index]   -- Local resource annotation of op output       : output[g,n](i1,...,in)
  | Operation QuantumOperation            -- Global resource consumption of an operation  : operation[g]
  | Identity                              -- No global resource consumption               : identity
  | Wire WireType                         -- Global resource consumption of a wire        : wire[w]
  | Sequence Index Index                  -- Composition in sequence of global resources  : i >> j
  | Parallel Index Index                  -- Composition in parallel of global resources  : i || j
  | BoundedSequence IVarId Index Index    -- Bounded composition in sequence              : seq[id < i] j
  | BoundedParallel IVarId Index Index    -- Bounded composition in parallel              : par[id < i] j
  deriving (Show, Eq)

instance Pretty Index where
  prettyPrec _ (IVar id) = id
  prettyPrec _ (Number n) = show n
  prettyPrec prec (Plus i j) = withinPar (prec > 5) $ prettyPrec 5 i ++ " + " ++ prettyPrec 5 j
  prettyPrec _ (Max i j) = "max(" ++ pretty i ++ ", " ++ pretty j ++ ")"
  prettyPrec prec (Mult i j) = withinPar (prec > 7) $ prettyPrec 7 i ++ " * " ++ prettyPrec 7 j
  prettyPrec prec (Minus i j) = withinPar (prec > 6) $ prettyPrec 6 i ++ " - " ++ prettyPrec 6 j
  prettyPrec prec (BoundedMax id i j) = withinPar (prec > 3) $ "max[" ++ id ++ " < " ++ pretty i ++ "]" ++ prettyPrec 3 j
  prettyPrec prec (BoundedMin id i j) = withinPar (prec > 3) $ "min[" ++ id ++ " < " ++ pretty i ++ "]" ++ prettyPrec 3 j
  prettyPrec prec (BoundedSum id i j) = withinPar (prec > 3) $ "sum[" ++ id ++ " < " ++ pretty i ++ "]" ++ prettyPrec 3 j
  prettyPrec _ i = undesugaredPanic "prettyPrec" $ show i

-- | The datatype of index contexts
type IndexContext = Set.HashSet IVarId

-- | The empty index context
emptyictx :: IndexContext
emptyictx = Set.empty
