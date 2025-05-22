{-
  Shor's algorithm
-}

--- Utils ---


-- discard multiple bits
{-
cdiscardMany = forall n. \x :: List[_<n+1] Bit.
  let cdiscardStep = lift forall step. \(_,q) :: ((),Bit).
    let _ = (force cdiscard @ n) q 
  in fold(cdiscardStep, [], x)
-}

-- discard multiple qubits
{-
qdiscardMany = forall n. \x :: List[_<n+1] Qubit.
  let qdiscardStep = lift forall step. \(_,q) :: ((),Qubit).
    let _ = (force qdiscard @ n) q 
  in fold(qdiscardStep, [], x)
-}

-- apply the Hadamard gate to n qubits at depth d
mapHadamard = forall n . forall d. \x :: List[_<n+1] Qubit{d} .
  let hadamardStep = lift forall step . \(qs,q) :: (List[_<step] Qubit{d+1}, Qubit{d}). qs:((force hadamard @ d) q)
  in fold(hadamardStep, [], x)

-- measure n qubits at depth d in the computational basis
mapMeasure = forall n. forall d. \x :: (List[i<n+1] Qubit{d}).
  let measureStep = lift forall step. \(bs,q) :: (List[i<step] Bit{d+1}, Qubit{d}). bs:((force meas @d) q)
  in fold(measureStep, [], x)

-- init n qubits to |0>
qinit0Many = forall n.
  let qinitStep = lift forall step. \(qs,u) :: (List[_<step] Qubit{0}, ()). qs:(force qinit0)
  in fold(qinitStep, [], force range @n+1)

-- init n qubits to |1>
qinit1Many = forall n.
  let qinitStep = lift forall step. \(qs,u) :: (List[_<step] Qubit{0}, ()). qs:(force qinit1)
  in fold(qinitStep, [], force range @(n+1))

-- invert the list of intermediate qubits at iteration iter
qrev = forall iter. forall d.
  \reg :: List[i<iter] Qubit{d+iter+i}.
    let revStep = lift forall step.
      \(rev, q) :: (List[i<step] Qubit{d+2*iter-(i+1)}, Qubit{d+2*iter-(step+1)}).
        rev:q in
    fold(revStep, [], reg)

--- iQFT Utils ---

-- invert the list of intermediate qubits at iteration iter
qrev = forall iter. forall d.
  \reg :: List[i<iter] Qubit{d+iter+i}.
    let revStep = lift forall step.
      \(rev, q) :: (List[i<step] Qubit{d+2*iter-(i+1)}, Qubit{d+2*iter-(step+1)}).
        rev:q in
    fold(revStep, [], reg)

-- apply the inv controlled rotation gate to the target qubit trg at iteration iter
rotate = forall d. forall iter. lift forall step.
  \((ctrls, trg), ctrl)::((List[i<step] Qubit{d+iter+i+1}, Qubit{d+iter+step}), Qubit{d+iter+step}).
    let (ctrl, trg) = (force invcr @(iter+1-step) @(d+iter+step) @(d+iter+step)) ctrl trg in
    (ctrls:ctrl, trg) -- :: (List[i<step+1] Qubit{d+iter+i+1}, Qubit{d+iter+step+1})

-- apply the inverse Quantum Fourier Transform to n+1 qubits at depth d
iqft :: ![0](forall[0,0] n. forall[0,0] d. List[_<n+1] Qubit{d} -o[n+1,0] List[i<n+1] Qubit{d+n+i+1})
iqft n d reg =
    let qftIter = lift forall iter. -- define the iteration of the QFT
      \(ctrls, trg)::(List[i<iter] Qubit{d+iter+i}, Qubit{d}).
        let revctrls = (force qrev @iter @d) ctrls in -- List[i<iter] Qubit{d+2*iter-(i+1)}
        let (ctrls, trg) = fold(force rotate @d @iter, ([], trg), revctrls) in
        -- note (ctrls, trg) :: (List[i<iter] Qubit{d+iter+i+1}, Qubit{d+2*iter})
        let trg = (force hadamard @(d+2*iter)) trg in
        ctrls:trg -- List[i<iter+1] Qubit{d+iter+1+i}
    in fold(qftIter, [], reg) -- List[i<n] Qubit{d+n+i}

--- Modular Arthimetic based on VBE ---

-- adder :: ![0](forall[0,0] n. (List[_<n+1] Qubit, List[_<n+1] Qubit, Qubit) -o[3*(n+1) + 1, 0] (List[_<n+1] Qubit, List[_<n+1] Qubit, Qubit))

-- subtractor :: ![0](forall[0,0] n. (List[_<n+1] Qubit, List[_<n+1] Qubit, Qubit) -o[3*(n+1) + 1, 0] (List[_<n+1] Qubit, List[_<n+1] Qubit, Qubit))

-- modAdder :: !(forall n. (List[_<n+1] Qubit, List[_<n+1] Qubit, Qubit) -o (List[_<n+1] Qubit, List[_<n+1] Qubit, Qubit))

-- cModMult :: !(forall n. (Qubit, List [_<n+1] Qubit, List [_<n+1] Qubit, List[_<n+1] Bit) -o[0,0] (Qubit, List [_<n+1] Qubit, List [_<n+1] Qubit, List[_<n+1] Bit))

-- iCModMult :: !(forall n. (Qubit, List [_<n+1] Qubit, List [_<n+1] Qubit, List[_<n+1] Bit) -o[0,0] (Qubit, List [_<n+1] Qubit, List [_<n+1] Qubit, List[_<n+1] Bit))

{-
modularExp :: !(forall n. (List [_<n+1] Qubit, List[_<n+1] Qubit, List[_<n+1] Bit) -o[2*(n+1),0] (List [_<n+1] Qubit, List[_<n+1] Qubit, List[_<n+1] Bit))
modularExp n (x, reg1, regMod) = 
    let modularStep = lift forall step . \((qs,reg0,reg1,regMod),q) :: ((List[_<step] Qubit, List[_<step] Qubit, List[_<step] Qubit, List[_<n+1] Bit), Qubit)
      let (x, reg1, reg0, regMod) = (force cModMult @n) q reg1 reg0 regMod in 
      let (x, reg1, reg0, regMod) = (force iCModMult @n) q reg0 reg1 regMod 
    in fold(modularStep, ([],reg0,reg1), x)
-}

{-
vbe :: ! (forall n. !((List[_<n+1] Qubit, List[_<n+1] Qubit) -o[0, 0] (List[_<n+1] Bit, (List[_<n+1] Bit))))
vbe n = box $ lift \(x, reg0, regMod) :: (List[_<n+1] Qubit, List[_<n+1] Qubit, List[_<n+1] Bit). 
    -- init register 1, I initialize it here in order to keep the unitarity 
    let reg1 = (force qinit1Many @n) in  
    -- Modular exponentiation 
    let (r, a, reg0, regMod) = (force modularExp @n) x reg1 reg0 regMod
    let _ = (force qdiscardMany @n) reg0 in -- TODO qdiscardMany
    (r, a, regMod)
-}

--- Shor circuit ---
--- !! Remember to add regMod/regQ to all subroutines ---
shor :: ![0](forall[0, 0] n. forall[0, 0] we. forall[0, 0] de. (forall[0, 0] d. Circ[we]((List[_ < n + 1] Qubit{d}, List[_ < n + 1] Qubit{d}, List [_<n+1] Bit), (List[_ < n + 1] Qubit{d + de}, List[_ < n + 1] Qubit{d + de}, List [_<n+1] Qubit))) -o[max(n + 1 + n + 1, we), 0] (List[i < n + 1] Bit{de + 2 * n + 3 + 1}, List[i < n + 1] Bit{1 + de + 1}, List [_<n+1] Bit))
shor n we de (oracle, regMod) = 
  -- prepare n qubits in the state |0> then apply hadamard 
  let x = (force mapHadamard @ n @ 0) (force qinit0Many @ n) in
  -- prepare n qubits in the state |0> 
  let w = force qinit0Many @ n in
  -- oracle function
  let (x, a, regMod) = apply(oracle @ 1, (x, w, regMod)) in
  -- phase estimation throught inverse QFT
  let r = (force iqft @ n @ 1 + de) x in 
  -- measure the results
  ((force mapMeasure @ n @ de + 2*n + 3) r, (force mapMeasure @ n @ 1 + de) a, regMod)
  -- |x>|w> -> (r, a), where r is the period and a is the base (a^r mod N)

-- shor @n vbe regMod 

-- The type of the function let the user choose which type of subroutine shor can perform
-- oracle is the subroutine that performs the modular exponentiation
-- regMod is the binary register of the number that we want to factorize
-- I do not assume any relation between p and q (N = pq)
