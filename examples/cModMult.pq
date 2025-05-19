{-
  Control Modular Multiplier
-}

-- c    = control bit
-- reg1 = x
-- regA = register ancilla
-- reg0 = regB
-- Possible outcomes: |c,x,regA,regB> -> |1,x,0,ax mod N> OR |0,x,0,x>

-- idea: 
-- scorrere su regA trovare il bit giusto usando range @ i poi fare toffoli sul bit trovato c e q come controlli, poi "ricostruire" regA

-- discard multiple qubits
{-
qdiscardMany = forall n. \x :: List[_<n+1] Qubit.
  let qdiscardStep = lift forall step. \(_,q) :: ((),Qubit).
    let _ = (force qdiscard @ n) q 
  in fold(qdiscardStep, [], x)
  -}

-- reverses a list of i qubits
rev = forall n. \list::List[_<n] Qubit.
  let revStep = lift forall step.\(qs, q) :: (List[_<step] Qubit, Qubit). qs:q
  in fold(revStep, [], list)

-- concatenate a list of n qubits and a list of m qubits (both lists can be empty)
concat :: !(forall n. forall m. (List [_<n] Qubit, List [_<m] Qubit) -o[0,0] (List [_<n + m] Qubit))
concat n m (a, b) = 
  let concatStep = lift forall step. \(a,q) :: (List[_<n+step] Qubit, Qubit). a:q
  in fold (concatStep, a, (force rev @m) b)  

-- i starts from 0
-- find the i-th qubit in a list
-- workaround: play with 1 more qubit at the end of rlist?
findBit :: !(forall n. forall i. (List[_<n+1] Qubit) -o[0,0] (List[_<i+1] Qubit, List[_<n-i+1] Qubit))
findBit n i regA =
  let regA = (force rev @ n+1) regA in -- in order to correctly search from the end
  let findStep = lift forall step. \((llist,rlist),_) :: ((List [_<step] Qubit, List [_<n-step] Qubit),()). 
    let rlist:q = rlist in
    let llist = llist:q in (llist,rlist) in
  let (llist,rlist) = fold(findStep, (regA,[]), (force range @ i+1)) in -- i >= 1
  (llist, (force rev @n-i+1) rlist) 

-- Single Bit-Wise Toffoli: toffili gate on the regA's k-th bit based on the i-th iteration of cMultModStep function
bitWiseToffoli :: !(forall n. forall i. (Qubit, Qubit, List[_<n+1] Qubit) -o[0,0] (Qubit, Qubit, List[_<n+1] Qubit))
bitWiseToffoli n i (c, q, regA) =
  let (llist,rlist) = (force findBit @ n @ i) regA in
  -- prendere quello da utilizzare -> ultimo della lista llist
  let (c,q,trg) = (force toffoli @ n) c q trg in
  -- reverse the list
  -- this operation reassamble the list in the opposite way because the findBit function
  let w = llist : trg in 
  let regA = (force concat @ i+1 @ n-i+1) w rlist in
  (c,q,regA)

-- brown Block: copy the x block into regB if the control bit is |0>
copyBlock :: !(forall n. (Qubit, List[_<n+1] Qubit, List[_<n+1] Qubit) -o[0,0] (Qubit, List[_<n+1] Qubit, List[_<n+1] Qubit))
copyBlock n (c, x, regB) = 
  -- First X gate for inverse CNOT
  let c = (force qnot @ n) c in
  -- Step function 
  let copyStep = lift forall step. \((c,xs,qs),(x,q)) :: ((Qubit, List[_<step] Qubit, List[_<step] Qubit),(Qubit,Qubit)).
    (force toffoli @ n) (c, x, q) in
  let (c,x,regB) = fold(copyStep, (c,x,[]),(x, regB)) in
  -- Second X gate for inverce CNOT
  let c = (force qnot @n) c in
  (c, x, regB)

-- Control Modular Multiplier --
cMultMod :: !(forall n. (Qubit, List [_<n+1] Qubit, List [_<n+1] Qubit) -o[0,0] (Qubit, List [_<n+1] Qubit, List [_<n+1] Qubit))
cMultMod n (c, x, regB) =
  -- Init working register (a*2^k)
  let regA = (force qinit0Many @ n) in
  -- Control Modular Step Function
  let cMultModStep = lift forall step. \((c,qs,regA,regB),q) :: (Qubit, List [_<step] Qubit, List[_<step] Qubit, Qubit).
      -- First toffoli on regA's k-th bit
      let (c,q,regA) = (force bitWiseToffoli @ n @ step) c q regA in 
      -- Modular Adder 
      let (regA,regB,x) = (force modAdder @ n) regA regB x in
      -- Second toffoli on regA's k-th bit
      (force bitWiseToffoli @ n @ step) c q regA in
  -- Fold loop
  let (c,x,regA,regB) = fold(cMultModStep, (c,[],regA,regB), x) in
  -- Copy x into regB if c = 0
  let _ = (qdiscard @ n) regA in -- qdiscardMany 
  ((force copyBlock @ n) c x regB) 
