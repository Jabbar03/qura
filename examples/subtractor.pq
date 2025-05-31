{-
  Basic quantum arithmetic operations.
  from Vlatko Vedral, Adriano Barenco and Artur Ekert. Quantum Networks for Elementary Arithmetic Operations. Physical Review A, 54(2):147-153, 1996.
  This implementation of quantum arithmetic is by no means state-of-the-art, but it employs ancillary qubits
  to perform the operations, so its analysis is interesting.
-}

--- list functions ---

-- reverses a list of i qubits
rev = forall n.\list::List[_<n] Qubit.
  let revStep = lift forall step.\(qs, q)::(List[_<step] Qubit, Qubit). qs:q
  in fold(revStep, [], list)

-- reverses a list of i pairs of qubits
revpair = forall n.\list::List[_<n] (Qubit,Qubit).
  let revStep = lift forall step.\(qs, q)::(List[_<step] (Qubit,Qubit), (Qubit,Qubit)). qs:q
  in fold(revStep, [], list)

-- zips two lists of i qubits
qzip = forall n . \(a,b) :: (List[_<n+1] Qubit, List[_<n+1] Qubit).
  let qzipStep = lift forall step. \((llist,reslist),relem) :: ((List[_<(n+1)-step] Qubit, List[_<step] (Qubit,Qubit)), Qubit).
    let ls:lelem = (llist !:: List[_<(n-step)+1] Qubit) in -- we can assume this because zipstep is only called by fold, where step < n+1
    let reslist = reslist : (lelem, relem) in
    (ls, reslist)
  in let (_, zippedlist) = (fold(qzipStep, (a,[]), b) :: (List[_<0] Qubit, List[_<n+1] (Qubit,Qubit)))
  in zippedlist

-- unzips a list of i pairs of qubits
qunzip = forall n . \a :: List[_<n] (Qubit,Qubit).
  let qunzipStep = lift forall step. \((leftList, rightList), pair) :: ((List[_<step] Qubit, List[_<step] Qubit), (Qubit,Qubit)).
    let (a,b) = pair in
    (leftList:a, rightList:b)
  in fold(qunzipStep, ([],[]), (force revpair @n) a)

interleave = forall n . \a :: List[_<n] (Qubit,Qubit). 
  let interleaveStep = lift forall step . \(reslist, pair) :: (List[_<step] ((Qubit,Qubit),Qubit), (Qubit,Qubit)).
    let c = apply(QInit0,()) in reslist:(pair,c)
  in fold(interleaveStep, [], (force revpair @n) a)

--- short-hands ---
-- We do not care about local metrics, so we preemptively instantiate them to 0

qnot = (force qnot @0)
cnot = (force cnot @0@0)
toffoli = (force toffoli @0@0@0)
qdiscard = (force qdiscard @0)

--- Circuits ---

-- CARRY (Fig. 3.i)
carry :: ![0]((Qubit, Qubit, Qubit, Qubit) -o[4, 0] (Qubit, Qubit, Qubit, Qubit))
carry (c, a, b, cnext) =
  let (a, b, cnext) = force toffoli a b cnext in
  let (a,b) = force cnot a b in
  let (c, b, cnext) = force toffoli c b cnext in
  (c, a, b, cnext)

icarry :: ![0]((Qubit, Qubit, Qubit, Qubit) -o[4, 0] (Qubit, Qubit, Qubit, Qubit))
icarry (c, a, b, cnext) =
  let (c, b, cnext) = force toffoli c b cnext in
  let (a,b) = force cnot a b in
  let (a, b, cnext) = force toffoli a b cnext in
  (c, a, b, cnext)

-- SUM (Fig. 3.ii)
csum :: ![0]((Qubit, Qubit, Qubit) -o[3, 0] (Qubit, Qubit, Qubit))
csum (c, a, b) =
  let (c, b) = force cnot c b in
  let (a, b) = force cnot a b in
  (c, a, b)

-- First part
subtractorFirstPhase :: ![0](forall[0,0] n. (Qubit, List[_<n+1] Qubit, List[_<n+1] Qubit) -o[3*n + 1, 0] (Qubit, List[_<n + 1] Qubit, List[_<n+1] Qubit))
subtractorFirstPhase n (overflow, a, b) =
  -- init
  let ab = (force qzip @ n) (a,b) in
  -- every first position is a, every second is b, every third is c
  let abc = (force interleave @ n+1) ab in 
  -- insert c_0 in front of the list of 3-tuple 
  let initialAcc = apply(QInit0,()) in
  
  -- fix the n_b+1 last qubit with overflow qubit for easier management
  let rest:((a,b),c) = abc in
  let _ = (force qdiscard) c in
  let abc = rest:((a,b),overflow) in

  -- subcircuit used in the first phase: carry followed by sum, carry discarded
  let csum = lift \(c,a,b,cnext) :: (Qubit,Qubit,Qubit,Qubit). 
      let (c,a,b) = force csum (c,a,b) in
      let (c,a,b,cnext) = force carry (c,a,b,cnext) in -- opposite icarry == carry
      (c,a,b) in
  let boxedSum = box csum in
  --step function:
  let subtractorStepFirst = lift $ forall step. \((cnext, reslist),((c,a),b)) :: ((Qubit, (List[_<step] (Qubit,Qubit))),((Qubit,Qubit),Qubit)).
    let (c,a,b) = apply(boxedSum, (c,a,b,cnext)) in
    (c, reslist:(a,b))
  in fold(subtractorStepFirst, (cfirst,[]), abc)

-- Second part
subtractorSecondPhase :: ![0](forall[0,0] n. (List[_<n+1] Qubit, List[_<n+1] Qubit) -o[3*n + 4, 0] (List[_<n+1] ((Qubit, Qubit), Qubit), Qubit))
subtractorSecondPhase n (a, b) =
  let subtractorStepSecond = lift forall step . \((reslist, c), ((a,b),cnext)) :: ((List[_<step] ((Qubit,Qubit),Qubit), Qubit), ((Qubit,Qubit),Qubit)) .
    let (c, a, b, cnext) = force icarry (c, a, b, cnext) in
    let _ = (force qdiscard) cnext in
    (reslist : ((c, a), b)) in
  let (reslist,clast) = fold(subtractorStepSecond, (overflow, []), abc) in
  (reslist,clast) -- note that the output triples are reversed

-- Subtractor
subtractor :: ![0](forall[0,0] n. (List[_<n+1] Qubit, List[_<n+1] Qubit, Qubit) -o[3*(n+1) + 1, 0] (List[_<n+1] Qubit, List[_<n+1] Qubit, Qubit))
subtractor n (a, b, overflow) =
  -- first part
  let (rest:((c,a),b),overflow) = (force subtractorFirstPhase @n) (overflow, a, b) in

  -- bottom of the valley / middle part
  let (c,a,b) = force csum (c,a,b) in
  let (a,b) = force cnot a b in

  -- final part
  let (overflow,final) = (force subtractorSecondPhase @n) () in -- ??

  -- parsing of the qubits
  let complete = (((force revpair @n) final) : (a,b)) in --add the first block back in
  let (ares,b) = (force qunzip @ n+1) complete in --separate a and b
  ((force rev @ n+1) ares, (force rev @ n+1) b, overflow) --rearrange the bits in the right order

-- This is the single gate invese subroutine of the adder subroutine
