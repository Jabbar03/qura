{-
  Shor's algorithm
-}

-- Utils

-- apply the Hadamard gate to n qubits at depth d
mapHadamard :: !(forall n. forall d. List[_<n+1] Qubit -o[0,0] List[_<n+1] Qubit)
mapHadamard n d (list) = 
  let hadamardStep = lift forall step . \(qs,q) :: (List[_<step] Qubit{d+1}, Qubit{d}). qs:((force hadamard @ d) q)
  in fold(hadamardStep, [], list)

-- operates a list of measurements on a list of qubits 
measureAll :: !(forall n. forall d. List[_<n+1] Qubit -o List[_<n+1] Bit)
measureAll n (list) = 
  let measureStep = lift forall step . \(bs,q) :: (List[_<step] Bit{d+1}, Qubit{d}). (force meas @ d) q 
  in fold(measureStep, [] , list)

-- init n qubits to |0>
qinit0Many = forall n.
  let qinitStep = lift forall step. \(qs,u) :: (List[_<step] Qubit{0}, ()). qs:(force qinit0)
  in fold(qinitStep, [], force range @n)

-- init n qubits to |1>
qinit1Many = forall n.
  let qinitStep = lift forall step. \(qs,u) :: (List[_<step] Qubit{0}, ()). qs:(force qinit1)
  in fold(qinitStep, [], force range @n)

-- inverse QFT
-- qft = iqft from complexity prespective (use qft for now) 

-- iqft :: ![0](forall[0,0] n. forall[0,0] d. List[i<n] Qubit{d} -o[n,0] List[i<n] Qubit{d+n+i})

-- invert the list of intermediate qubits at iteration iter
qrev = forall iter. 
  \reg :: List[i<iter] Qubit.
    let revStep = lift forall step.
      \(rev, q) :: (List[i<step] Qubit, Qubit).
        rev:q in
    fold(revStep, [], reg)

-- apply the controlled rotation gate to the target qubit trg at iteration iter
rotate = forall iter. lift forall step.
  \((ctrls, trg), ctrl)::((List[i<step] Qubit, Qubit), Qubit).
    let (ctrl, trg) = (force cr @(iter+1-step)) ctrl trg in
    (ctrls:ctrl, trg) -- :: (List[i<step+1] Qubit{d+iter+i+1}, Qubit{d+iter+step+1})

-- apply the Quantum Fourier Transform to n qubits at depth d
qft :: ![0](forall[0,0] n. List[i<n] Qubit{d} -o[n,0] List[i<n] Qubit)
qft n reg =
    let qftIter = lift forall iter. -- define the iteration of the QFT
      \(ctrls, trg)::(List[i<iter] Qubit, Qubit).
        let revctrls = (force qrev @iter) ctrls in -- List[i<iter] Qubit{d+2*iter-(i+1)}
        let (ctrls, trg) = fold(force rotate @iter, ([], trg), revctrls) in
        -- note (ctrls, trg) :: (List[i<iter] Qubit{d+iter+i+1}, Qubit{d+2*iter})
        let trg = (force hadamard) trg in
        ctrls:trg -- List[i<iter+1] Qubit{d+iter+1+i}
    in fold(qftIter, [], reg) -- List[i<n] Qubit{d+n+i}

-- modular arthimetic based on VBE 

-- adder :: ![0](forall[0,0] n. (List[_<n+1] Qubit, List[_<n+1] Qubit, Qubit) -o[3*(n+1) + 1, 0] (List[_<n+1] Qubit, List[_<n+1] Qubit, Qubit))

-- subtractor :: ![0](forall[0,0] n. (List[_<n+1] Qubit, List[_<n+1] Qubit, Qubit) -o[3*(n+1) + 1, 0] (List[_<n+1] Qubit, List[_<n+1] Qubit, Qubit))

-- modAdder :: !(forall n. (List[_<n+1] Qubit, List[_<n+1] Qubit, Qubit) -o (List[_<n+1] Qubit, List[_<n+1] Qubit, Qubit))

-- cMultMod :: 
-- iCMultMod :: 

-- modularExp :: !(forall n. (List [_<n+1] Qubit, List[_<n+1] Qubit) -o[2*(n+1),0] (List [_<n+1] Qubit, List[_<n+1] Qubit))
{-
modularExp n (x, reg1) = 
    let cmultmodStep = lift forall step . \((qs,reg0,reg1),q) :: (List[_<step] Qubit, List[_<step] Qubit)
    let (x, reg1, reg0) = (force cMultMod @n) q reg1 reg0 in 
    let (x, reg1, reg0) = (force iCMultMod @n) q reg0 reg1 
    in fold(cmultmodStep, ([],reg0,reg1), x)
-}

{-
vbe :: ! (forall n. !((List[_<n+1] Qubit, List[_<n+1] Qubit) -o[7*(n+1), 0] (List[_<n+1] Bit, (List[_<n+1] Bit))))
vbe n = box $ lift \(x, reg0) :: (List[_<n+1] Qubit, List[_<n+1] Qubit). 
    -- init register 1, I initialize it here in order to keep the unitarity 
    let reg1 = (force qinit1Many @n) in  
    -- Modular exponentiation 
    let (a, r, reg0) = (force modularExp @n) x reg1 reg0
    let _ = (force qdiscard @n) reg0 in 
    (a, r)
-}

-- Shor circuit --
shor :: !(forall n. forall we. Circ[we](List[_<n+1] Qubit, List[_<n+1] Qubit) -o[0,0] (List[_<n+1] Bit)
shor n oracle = 
  -- init n qubits to |0> then apply hadamard 
  let x = (force mapHadamard @n) (force qinit0Many @n) in
  -- init n qubits to |0> 
  let w = (force qinit0Many @n) in
  -- oracle function
  let (x, a) = (force oracle @n) x w in
  -- estemation of the fase with inverse QFT
  let r = (force qft @n) x in -- iqft instead of qft
  -- measure the results
  -- |x>|w> -> (r, a),  where r is the period and a is the base (a^r mod N)
  (force measureAll @n) r 

-- forall n. shor vbe @n 

-- The type of the function let the user choose what type of subroutine shor can execute
-- change the oracle subroutine with another implementation, call shor with another subroutine instead of vbe
-- I do not assume any relation between p and q (N = pq)
