{-
  Shor skeleton implementation, I do not assume any optimization for the factorization algorithm
-}

-- Utils

-- apply the Hadamard gate to n qubits at depth d
mapHadamard :: !(forall n. forall d. :: List[_<n+1] Qubit -o[0,0] List[_<n+1] Qubit)
mapHadamard n d (list) = 
  let hadamardStep = lift forall step . \(qs,q) :: (List[_<step] Qubit{d+1}, Qubit{d}). qs:((force hadamard @ d) q)
  in fold(hadamardStep, [], list)

-- operates a list of measurements on a list of qubits 
measureAll :: !(forall n. forall d. :: List[_<n+1] Qubit -o List[_<n+1] Bit)
measureAll n (list) = 
  let measureStep = lift forall step . \(bs,q) :: (List[_<step] Bit{d+1}, Qubit{d}). (force meas @ d) q 
  in fold(measureStep, [] , list)

qinitMany :: !(forall n. Circ(![1] Qubit{n}) -o List[_<n] Qubit)
qinitMany n f = 
  let qinitStep = lift forall step. \(qs,u) :: (List[_<step] Qubit{0}, ()). qs:(force f)
  in fold(qinitStep, [], force range @n)

-- inverse QFT

iqft :: !()
  iqft =

-- modular arthimetic based on VBE 

-- adder :: done 
-- subtractor :: wip 
-- modAdder :: kinda done 
-- cMultMod :: 
-- iCMultMod :: 

modularExp :: !(forall n. (List [_<n+1] Qubit, List[_<n+1] Qubit) -o ())
modularExp n (x, reg1) = 
    let cmultmodStep = lift forall step . \((qs,reg0,reg1),q) :: (List[_<step] Qubit, List[_<step] Qubit)
    let (x, reg1, reg0) = (force cMultMod @n) q reg1 reg0 in 
    let (x, reg1, reg0) = (force iCMultMod @n) q reg0 reg1 
    in fold(cmultmodStep, ([],reg0,reg1), x)

vbe = forall n. 
  box $ lift \(x, reg0) :: (List[_<n+1] Qubit, List[_<n+1] Qubit)
    -- init register 1, I initialize it here in order to keep the unitarity 
    let reg1 = (force qinitMany @n) qinit1 in  
    -- Modular exponentiation 
    (a, r, w) = (force modularExp @n) x reg1 reg0

-- Shor circuit --
shor :: !(forall n. forall os. Circ[os](List[_<n+1] Qubit, List[_<n+1] Qubit) -o (List[_<n+1] Bit)
shor n oracle = 
  -- init n qubits to |0> then hadamard on all 
  let x = (force mapHadamard @n) (force qinitMany @n) qinit0 in
  -- init n qubits to |0> 
  let w = (force qinitMany @n) qinit0 in
  -- oracle function
  let (x, a) = (force oracle @n) x w in
  -- estemation of the fase with inverse QFT
  let r = (force iqft @n) x in
  -- measure the results
  -- |x>|w> -> (r, a),  where r is the period and a is the base (a^r mod N)
  (force measureAll @n) r 

-- The type of the function let the user choose what type of subroutine shor can execute
-- change the oracle subroutine with another implementation, call shor with another subroutine instead of vbe
