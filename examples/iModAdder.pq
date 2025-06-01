{-
  Basic quantum arithmetic operations.
  from Vlatko Vedral, Adriano Barenco and Artur Ekert. Quantum Networks for Elementary Arithmetic Operations. Physical Review A, 54(2):147-153, 1996.
  This implementation of quantum arithmetic is by no means state-of-the-art, but it employs ancillary qubits
  to perform the operations, so its analysis is interesting.
-}


--- Inverse Modular Adder ---
{- plan: (x* means ancilla, -1 means inverse function) 
  input: a b N* 0* 
  1. a-b 
  2. a-b+a 
  3. a-b+a-x*t
  4. a-b+a-x*t+x*t
  5. a-b+a-x*t+x*t-a
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

-- reverses a list of i triplets of qubits
revtriplets = forall n. \list::List[_<n] ((Qubit,Qubit),Qubit).
  let revStep = lift forall step.\(qs, q)::(List[_<step] ((Qubit,Qubit),Qubit), ((Qubit,Qubit),Qubit)). qs:q
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


-- Adder utilities 

-- CARRY (Fig. 3.i)
carry :: ![0]((Qubit, Qubit, Qubit, Qubit) -o[4, 0] (Qubit, Qubit, Qubit, Qubit))
carry (c, a, b, cnext) =
  let (a, b, cnext) = force toffoli a b cnext in
  let (a,b) = force cnot a b in
  let (c, b, cnext) = force toffoli c b cnext in
  (c, a, b, cnext)

-- REVERSE CARRY
icarry :: ![0]((Qubit, Qubit, Qubit, Qubit) -o[4, 0] (Qubit, Qubit, Qubit, Qubit))
icarry (c, a, b, cnext) =
  let (c, b, cnext) = force toffoli c b cnext in
  let (a,b) = force cnot a b in
  let (a, b, cnext) = force toffoli a b cnext in
  (c, a, b, cnext)

-- SUM (Fig. 3.ii)
csum :: ![0]((Qubit, Qubit, Qubit) -o[3, 0] (Qubit, Qubit, Qubit))
csum (c, a, b) =
  let (a,b) = force cnot a b in
  let (c, b) = force cnot c b in
  (c, a, b)

-- (Fig. 2, first half)
adderFirstPhase :: ![0](forall[0, 0] n. (List[_ < n + 1] Qubit, List[_ < n + 1] Qubit, Qubit) -o[1 + (n + 1) * 3 + 1, 0] (List[_ < (n + 1) - 1 + 1] ((Qubit, Qubit), Qubit), Qubit))
adderFirstPhase n (a, b, overflow) =
  let ab = (force qzip @n) (a,b) in
  let abc = (force interleave @ n+1) ab in --every first position is a, every second is b, every third is c
  let initialAcc = apply(QInit0,()) in
  
  -- Fix the n_b+1 last qubit
  let rest:((a,b),c) = abc in
  let _ = (force qdiscard) c in
  let abc = rest:((a,b),overflow) in

  let adderStepFirst = lift forall step . \((reslist, c), ((a,b),cnext)) :: ((List[_<step] ((Qubit,Qubit),Qubit), Qubit), ((Qubit,Qubit),Qubit)) .
    let (c, a, b, cnext) = force carry (c, a, b, cnext) in
    (reslist : ((c, a), b), cnext) in
  let (reslist,overflow) = fold(adderStepFirst, ([], initialAcc), abc) in
  (reslist,overflow) -- note that the output triples are reversed

adderSecondPhase :: ![0](forall[0,0] n. (Qubit, List[_<n] ((Qubit, Qubit), Qubit)) -o[3*n + 1, 0] (Qubit, List[_<n] (Qubit, Qubit)))
adderSecondPhase n (cfirst, abc) =
  --subcircuit used in the second phase: carry followed by sum, carry discarded:
  let csum = lift \(c,a,b,cnext) :: (Qubit,Qubit,Qubit,Qubit). 
      let (c,a,b,cnext) = force icarry (c,a,b,cnext) in
      let (c,a,b) = force csum (c,a,b) in
      let _ = (force qdiscard) cnext in
      (c,a,b) in
  let boxedSum = box csum in
  --step function:
  let adderStepSecond = lift $ forall step. \((cnext, reslist),((c,a),b)) :: ((Qubit, (List[_<step] (Qubit,Qubit))),((Qubit,Qubit),Qubit)).
    let (c,a,b,cnext) = apply(boxedSum, (c,a,b,cnext)) in 
    (c, reslist:(a,b))
  in fold(adderStepSecond, (cfirst,[]), abc)

-- ADDER
adder :: ![0](forall[0,0] n. (List[_<n+1] Qubit, List[_<n+1] Qubit, Qubit) -o[1 + (n + 1) * 3 + 1, 0] (List[_<n+1] Qubit, List[_<n+1] Qubit, Qubit))
adder n (a, b, overflow) =
  let (rest:((c,a),b),overflow) = (force adderFirstPhase @n) (a,b,overflow) in 
  -- overflow = b_n+1 
  let (a,b) = force cnot a b in
  let (c,a,b) = force csum (c,a,b) in
  let (lastc, final) = (force adderSecondPhase @n) (c, rest) in
  let _ = (force qdiscard) lastc in
  let complete = (((force revpair @n) final) : (a,b)) in --add the first block back in
  let (ares,b) = (force qunzip @ n+1) complete in --separate a and b
  ((force rev @ n+1) ares, (force rev @ n+1) b, overflow) --rearrange the bits in the right order

--- Subtractor ---

-- First part
subtractorFirstPhase :: ![0](forall[0,0] n. List[_<n] (Qubit, Qubit) -o[3*n+1, 0] (List[_<n] ((Qubit,Qubit),Qubit),Qubit))
subtractorFirstPhase n ab =
  -- every first position is a, every second is b, every third is c
  let abc = (force interleave @ n) ab in 
  -- insert c_0 in front of the list of 3-tuple 
  let initialAcc = (force qinit0) in
  
  -- subcircuit used in the first phase: carry followed by sum, carry discarded
  let csum = lift \(c,a,b,cnext) :: (Qubit,Qubit,Qubit,Qubit). 
      let (c,a,b) = force csum (c,a,b) in
      let (c,a,b,cnext) = force carry (c,a,b,cnext) in -- opposite icarry == carry
      (c,a,b,cnext) in
  let boxedSum = box csum in
  --step function:
  let subtractorStepFirst = lift $ forall step. \((reslist,cnext),((c,a),b)) :: (((List[_<step] ((Qubit,Qubit),Qubit)),Qubit),((Qubit,Qubit),Qubit)).
    let (c,a,b,cnext) = apply(boxedSum, (c,a,b,cnext)) in
    (reslist:((c,a),b),cnext)
  in fold(subtractorStepFirst, ([],initialAcc), (force revtriplets @n) abc) -- since the stepfunc will reverse the list we premtivily reverse it

-- Second part
subtractorSecondPhase :: ![0](forall[0,0] n. (List[_<n] ((Qubit,Qubit),Qubit),Qubit) -o[3*n+1, 0] (List[_<n] (Qubit, Qubit), Qubit))
subtractorSecondPhase n (list, clast) =
  let subtractorStepSecond = lift forall step . \((reslist, c), ((a,b),cnext)) :: ((List[_<step] (Qubit,Qubit), Qubit), ((Qubit,Qubit),Qubit)) .
    let (c, a, b, cnext) = force icarry (c, a, b, cnext) in
    let _ = (force qdiscard) cnext in
    (reslist:(a,b),c) in
  let (reslist,cfirst) = fold(subtractorStepSecond, ([],clast), list) in
  (reslist,cfirst) -- note that the output triples are reversed

-- Subtractor
subtractor :: ![0](forall[0,0] n. (List[_<n+1] Qubit, List[_<n+1] Qubit, Qubit) -o[3*(n+1) + 1, 0] (List[_<n+1] Qubit, List[_<n+1] Qubit, Qubit))
subtractor n (a, b, overflow) =
  -- first part
  let ab = (force qzip @n) (a,b) in
  -- this operation will be done n times (on list_n+1) so we save up the last pair (a,b) then single handedly manage it
  let ab:(alast,blast) = ab in
  let (list,clast) = (force subtractorFirstPhase @n) ab in
  
  -- bottom of the valley, individually handle
  let (clast,alast,blast) = force csum (clast,alast,blast) in
  let (alast,blast) = force cnot alast blast in
  let (clast,alast,blast,overflow) = force icarry (clast,alast,blast,overflow) in

  -- final part: carry operation and discard of c qubits
  -- input: list_n+1 triplets + overflow
  -- output: list_n+1 pairs + overflow
  let (list,cfirst) = (force subtractorSecondPhase @n) ((force revtriplets @n) list, clast) in

  -- discard the last carry qubit 
  let _ = force qdiscard cfirst in
  -- reassemble the last pair into the list
  let list = list:(alast,blast) in
  -- parsing of the qubits
  let (a,b) = (force qunzip @ n+1) list in --separate a and b
  ((force rev @ n+1) a, (force rev @ n+1) b, overflow) --rearrange the bits in the right order

-- cancel Block if temp bit is set to 0 
-- may implemented with swap operation
deleteBlock :: ![0](forall[0,0] n. (List[_<n+1] Qubit, Qubit) -o[n + 1 + 1,0] (List[_<n+1] Qubit, Qubit))
deleteBlock n (list, temp) = 
  let deleteStep = lift forall step. \((qs,temp), q) :: ((List[_<step] Qubit, Qubit), Qubit). 
    let (temp, q) = (force cnot) temp q in (qs:q, temp)
  in fold(deleteStep, ([],temp), list)

--- Inverse Modular Adder ---
iModAdder :: ![0](forall[0,0] n. (List[_<n+1] Qubit, List[_<n+1] Qubit, List[_<n+1] Qubit) -o[4*(n + 1) + 3,0] (List[_<n+1] Qubit, List[_<n+1] Qubit, List[_<n+1] Qubit))
iModAdder n (a, b, x) = 
  -- init overflow qubit
  let overflow = (force qinit0) in
  -- init temp qubit
  let temp = (force qinit0) in 
  
  let (a, ab, overflow) = (force subtractor @n) (a, b, overflow) in -- a-b
  -- Make temp qbit return to |0>
  let (overflow,temp) = (force cnot) overflow temp in 

  let (a, aba, overflow) = (force adder @n) (a, ab, overflow) in -- a-b+a

  let (tx, temp) = (force deleteBlock @n) (x, temp) in -- cancel block (CNOTs??)
  let (tx, abatx, overflow) = (force subtractor @n) (tx, aba, overflow) in -- a-b+a-t*x
  let (x, temp) = (force deleteBlock @n) (tx, temp) in
  let (x, abatxtx, overflow) = (force adder @n) (x, abatx, overflow) in -- a-b+a-t*x+t*x

  -- Inverse CNOT
  let overflow = (force qnot) overflow in
  let (overflow,temp) = (force cnot) overflow temp in 
  let overflow = (force qnot) overflow in

  let (a, abatxtxa) = (force subtractor @n) (a, abatxtx, overflow) in -- a-b+a-t*x+t*x-a
  let _ = (force qdiscard) temp in
  (a, abatxtxa, x)
