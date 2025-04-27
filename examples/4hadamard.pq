{-
Hadamards on an list of max 4 qubits - global width & local depth 
-}

hada4 :: ![0](forall[0,0] d. (List[_<4] Qubit{d}) -o[4,0] (List[_<4] Qubit{d+1})) -- definition
hada4 = forall d. \list :: List[_ < 4] Qubit{d}. 
  let hadaStep = lift forall step. \(qs,q) :: (List[_<step] Qubit{d+1}, Qubit{d}). 
  let q = (force hadamard @d) q in qs:q
  in fold(hadaStep, [], list) 

-- call hada4 on a list of n lists of 4 qubits
myF = forall d. forall n. \x :: List[_ < n] (List[_ < 4] Qubit{d}). -- cannot do a list of list of qubit?
  let hadaAll = lift forall m. \(qs,q) :: (List[_<m] Qubit{d+1}, Qubit{d}). qs:(force hada4 @d) 
  in fold(hadaAll, [], x)

{- 
How i see fold excecution:
fold revStep, [], list
fold revStep, [], revStep list -> 
fold revStep, [], revStep q:qs -> 
fold revStep, [], qs:q1, 
fold revStep, [], (revStep qs):q1 -> 
fold revStep, [], (revStep q2:qs):q1 -> 
fold revStep, [], qs:q2:q1 -> 
...
fold revStep, [], qn:qn-1:...:q2:q1
-}


