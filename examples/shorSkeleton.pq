{-
  Shor Skeleton
-}

-- Utils

-- apply the Hadamard gate to n qubits at depth d
mapHadamard = forall n . \x :: List[_<n+1] Qubit.
  let hadamardStep = lift forall step . \(qs,q) :: (List[_<step] Qubit, Qubit). qs:((force hadamard @n) q)
  in fold(hadamardStep, [], x)

-- measure n qubits at depth d in the computational basis
mapMeasure = forall n. \x :: List[_<n+1] Qubit.
  let measureStep = lift forall step. \(bs,q) :: (List[_<step] Bit, Qubit). bs:((force meas @ 0) q)
  in fold(measureStep, [], x)

-- init n qubits to |0>
qinit0Many = forall n.
  let qinitStep = lift forall step. \(qs,u) :: (List[_<step] Qubit, ()). qs:(force qinit0)
  in fold(qinitStep, [], force range @(n+1))

-- init n qubits to |1>
qinit1Many = forall n.
  let qinitStep = lift forall step. \(qs,u) :: (List[_<step] Qubit, ()). qs:(force qinit1)
  in fold(qinitStep, [], force range @(n+1))

-- iQFT

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
    let (ctrl, trg) = (force cr @(iter+1-step) @0 @0) ctrl trg in
    (ctrls:ctrl, trg) -- :: (List[i<step+1] Qubit{d+iter+i+1}, Qubit{d+iter+step+1})

-- apply the Quantum Fourier Transform to n qubits at depth d
iqft :: ![0](forall[0,0] n. List[_<n+1] Qubit -o[n+1,0] List[_<n+1] Qubit)
iqft n reg =
    let qftIter = lift forall iter. -- define the iteration of the QFT
      \(ctrls, trg)::(List[i<iter] Qubit, Qubit).
        let revctrls = (force qrev @iter) ctrls in -- List[i<iter] Qubit{d+2*iter-(i+1)}
        let (ctrls, trg) = fold(force rotate @iter, ([], trg), revctrls) in
        -- note (ctrls, trg) :: (List[i<iter] Qubit{d+iter+i+1}, Qubit{d+2*iter})
        let trg = (force hadamard @n) trg in
        ctrls:trg -- List[i<iter+1] Qubit{d+iter+1+i}
    in fold(qftIter, [], reg) -- List[i<n] Qubit{d+n+i}

-- Shor circuit --
shor :: ![0](forall[0,0] n. forall[0,0] we. Circ[we]((List[_<n+1] Qubit, List[_<n+1] Qubit),(List[_<n+1] Qubit, List[_<n+1] Qubit)) -o[max(n + 1 + n + 1, we),0] (List[_<n+1] Bit, List[_<n+1] Bit))
shor n we oracle = 
  -- init n qubits to |0> then apply hadamard 
  let x = (force mapHadamard @ n) (force qinit0Many @ n) in
  -- init n qubits to |0>  x in
  let w = force qinit0Many @ n in
  -- oracle function
  let (x, a) = apply(oracle, (x, w)) in
  -- estemation of the fase with inverse QFT
  let r = (force iqft @n) x in -- iqft instead of qft
  -- measure the results
  ((force mapMeasure @n) r, (force mapMeasure @n) a)
  -- |x>|w> -> (r, a),  where r is the period and a is the base (a^r mod N)
