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

-- QUESTION i starts from 0 or 1 ???
-- QUESTION should i reverse the list before the stepFunction ???
findBit :: !(forall n. forall i. (List[_<n+1] Qubit) -o[0,0] (List[_<i-1] Qubit,Qubit, List[_<n-i+1] Qubit))
findBit n i regA =
  -- rev the list ???
  -- let regA = (qrev @ n) regA in
  let findStep = lift forall step. \((llist,rlist),q). :: ((List [_<step-1] Qubit, List [_<n-step+1] Qubit),Qubit). q in 
  fold(findStep, [], range @ i) 
  

-- Single Bit-Wise Toffoli: toffili gate on the regA's k-th bit based on the i-th iteration of cMultModStep function
bitWiseToffoli :: !(forall n. forall i. (Qubit, Qubit, List[_<n+1] Qubit) -o[0,0] ((Qubit, Qubit, List[_<n+1] Qubit)))
bitWiseToffoli n i (c,q,regA) =
  let (llist,trg,rlist) = (force findBit @ n @ i) regA in
  let (c,q,trg) = (force toffoli @ n) c q trg in
  -- reverse the list
  -- this operation reassamble the list in the opposite way because the findBit function
  let regA = rlist : trg : llist in 
  (c,q,regA)

-- brown Block: copy the x block into regB if the control bit is |0>
copyBlock :: !(forall n. (Qubit, List[_<n+1] Qubit, List[_<n+1] Qubit) -o[0,0] (Qubit, List[_<n+1] Qubit, List[_<n+1] Qubit))
copyBlock c x regB = 
  -- First X gate for inverce CNOT
  let c = (force qnot @ n) c
  -- Step function 
  let copyStep = lift forall step. \((c,xs,qs),(x,q)) :: ((Qubit, List[_<step],List[_<step]),(Qubit,Qubit))
    let (c,x,q) = (force toffoli @ n) c x q in 
  let (c,x,regB) = fold(copyStep, (c,x,[]),(x,regB)) in
  -- Second X gate for inverce CNOT
  let c = (force qnot @n) c in 
  (c, x, regB)

cMultMod :: !(forall n. (Qubit, List [_<n+1] Qubit, List [_<n+1] Qubit) -o[0,0] (Qubit, List [_<n+1] Qubit, List [_<n+1] Qubit))
cMultMod n (c, x, regB) =
  -- Init working register (a*2^k)
  let regA = (force qinit0Many @ n) in
  -- Control Modular Step Function
  let cMultModStep = lift forall step. \((c,qs,regA,regB),q). (Qubit, List [_<step], List[_<step],Qubit)
      -- First toffoli on regA's k-th bit
      let (c,q,regA) = (force bitWiseToffoli @ n @ step) c q regA in 
      -- Modular Adder 
      let (regA,regB,x) = (force modAdder @ n) regA regB x in
      -- Second toffoli on regA's k-th bit
      let (c,q,regA) = (force bitWiseToffoli @ n @ step) c q regA in 
  -- Fold loop
  let (c,x,regA,regB) = fold(cMultModStep, (c,[],regA,regB), x) in
  -- Copy x into regB if c = 0
  let _ = (qdiscard @ n) regA in -- TODO qdiscardMany
  ((force copyBlock @ n) c x regB) 
