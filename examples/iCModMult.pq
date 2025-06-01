{- 
  Inverse Control Modular Multiplier 
-}

--- short-hands ---
qnot = (force qnot @0)
cnot = (force cnot @0@0)
toffoli = (force toffoli @0@0@0)
qdiscard = (force qdiscard @0)
ccnot = (force ccnot @0 @0)

--- General Utils ---

-- discard multiple qubits
qdiscardMany = forall n. \x :: List[_<n+1] Qubit.
  let qdiscardStep = lift forall step. \(_,q) :: ((),Qubit).
    force qdiscard q 
  in fold(qdiscardStep, (), x)

-- initialize a qubit |0> from a bit
qinitFromBit :: ![0](Bit -o[2,0] (Bit, Qubit))
qinitFromBit b =
  let q = force qinit0 in force ccnot b q

-- initialize qubits register from a bit register
qinitFromBits :: ![0](forall[0, 0] n. List[i < n + 1] Bit -o[max[step < n + 1]2 + step + step + (n + 1) - (step + 1), 0] (List[i < n + 1] Bit, List[i < n + 1] Qubit))
qinitFromBits n bs =
  let qinitStep = lift forall step. \((bs,qs), b) :: ((List[i<step] Bit, List[i<step] Qubit), Bit).
    let (b, q) = force qinitFromBit b in
    (bs:b, qs:q)
  in fold(qinitStep, ([],[]), bs)

-- measure n qubits at depth d in the computational basis
mapMeasure = forall n. \x :: (List[i<n+1] Qubit).
  let measureStep = lift forall step. \(bs,q) :: (List[i<step] Bit, Qubit). bs:((force meas @0) q)
  in fold(measureStep, [], x)

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


-- Adder utilities 

-- carry (Fig. 3.i)
carry :: ![0]((Qubit, Qubit, Qubit, Qubit) -o[4, 0] (Qubit, Qubit, Qubit, Qubit))
carry (c, a, b, cnext) =
  let (a, b, cnext) = force toffoli a b cnext in
  let (a,b) = force cnot a b in
  let (c, b, cnext) = force toffoli c b cnext in
  (c, a, b, cnext)

-- reverse carry
icarry :: ![0]((Qubit, Qubit, Qubit, Qubit) -o[4, 0] (Qubit, Qubit, Qubit, Qubit))
icarry (c, a, b, cnext) =
  let (c, b, cnext) = force toffoli c b cnext in
  let (a,b) = force cnot a b in
  let (a, b, cnext) = force toffoli a b cnext in
  (c, a, b, cnext)

-- sum (Fig. 3.ii)
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

-- Adder
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


--- Subtractor Utils ---

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
  -- Make temp qubit return to |0>
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

--- Control Modular Multiplier Utils ---

-- init n qubits to |0>
qinit0Many = forall n.
  let qinitStep = lift forall step. \(qs,u) :: (List[_<step] Qubit, ()). qs:(force qinit0)
  in fold(qinitStep, [], force range @n+1)

-- concatenate a list of n qubits and a list of m qubits (both lists can be empty)
concat :: ![0](forall[0,0] n. forall[0,0] m. (List [_<n] Qubit, List [_<m] Qubit) -o[m + n, 0] (List [_<n + m] Qubit))
concat n m (a, b) = 
  let concatStep = lift forall step. \(a,q) :: (List[_<n+step] Qubit, Qubit). a:q
  in fold (concatStep, a, (force rev @m) b)  

-- i starts from 0
-- find the i-th qubit in a list

findBit :: ![0](forall[0, 0] n. forall[0, 0] i. List[_ < n + 1] Qubit -o[max[step < i + 1]step + 1 + (n - step + 1) - 1, 0] (List[_ < i + 1] Qubit, List[_ < (n + 1) - (i + 1)] Qubit))
findBit n i regA =
  let regA = (force rev @ n+1) regA in -- in order to correctly search from the end
  let findStep = lift forall step. \((llist,rlist),_) :: ((List [_<step] Qubit, List [_<(n+1)-step] Qubit),()). 
    let rlist:q = (rlist !:: List[_<(n-step)+1] Qubit) in -- unsafe behaviour, coercition type
    let llist = llist:q in (llist,rlist !:: List[_<(n+1)-(step+1)] Qubit) in -- unsafe behaviour, coercition type
  let (llist,rlist) = fold(findStep, ([],regA), (force range @ i+1)) in -- i >= 1
  (llist, (force rev @(n+1)-(i+1)) rlist) 

-- Single Bit-Wise Toffoli: toffili gate on the regA's k-th bit based on the i-th iteration of cMultModStep function
bitWiseToffoli :: ![0](forall[0, 0] n. forall[0, 0] i. (Qubit, Qubit, List[_ < n + 1] Qubit) -o[(max[step < i + 1]step + 1 + (n - step + 1) - 1) + 2, 0] (Qubit, Qubit, List[_ < n + 1] Qubit))
bitWiseToffoli n i (c, q, regA) =
  -- find the qubit for the toffoli operation (placed at the end of llist)
  let (llist,rlist) = (force findBit @ n @ i) regA in
  -- get last qubit from llist (target)
  let llist:trg = llist in 
  let (c,q,trg) = force toffoli c q trg in
  -- reverse the list: this operation reassamble the list in the opposite way because of the findBit function 
  let w = llist : trg in 
  let regA = (force concat @ i+1 @ (n+1)-(i+1)) (w, rlist) in
  (c,q,regA !:: List[_<n+1] Qubit)

-- brown Block: move the x block into regB if the control bit is |0>
moveBlock :: ![0](forall[0,0] n. (Qubit, List[_<n+1] Qubit, List[_<n+1] Qubit) -o[2*n + 3,0] (Qubit, List[_<n+1] Qubit, List[_<n+1] Qubit))
moveBlock n (c, x, regB) = 
  -- First X gate for inverse CNOT
  let c = force qnot c in
  -- Step function 
  let moveStep = lift forall step. \((c,xs,qs),(x,q)) :: ((Qubit, List[_<step] Qubit, List[_<step] Qubit),(Qubit,Qubit)).
    let (c,x,q) = (force toffoli) c x q in (c,xs:x,qs:q) in
  let (c,x,regB) = fold(moveStep, (c,[],[]),(force qzip @n) (x, regB)) in
  -- Second X gate for inverse CNOT
  let c = force qnot c in
  (c, (force rev @n+1) x, (force rev @n+1) regB)

--- Control Modular Multiplier ---
-- The operation on regMod/regQ are done inside the step function in order to have a correct depth approximation of the register 
iCModMult :: ![0](forall[0, 0] n. (Qubit, List[_ < n + 1] Qubit, List[_ < n + 1] Qubit, List[_ < n + 1] Bit) -o[max[step < n + 1]max((max[step < step + 1]step + 1 + (n - step + 1) - 1) + 2 + step + n + 1 + n + 1 + n + 1, max(4 * (n + 1) + 3 + step + n + 1 + 2, max(n + 1 + n + 1 + step + n + 1 + 1 + n + 1 + 1, (max[step < step + 1]step + 1 + (n - step + 1) - 1) + 2 + step + n + 1 + n + 1))) + (n + 1) - (step + 1), 0] (Qubit, List[_ < n + 1] Qubit, List[_ < n + 1] Qubit, List[_ < n + 1] Bit))
iCModMult n (c, x, regB, regMod) =
  -- Init working register (a*2^k)
  let regA = (force qinit0Many @ n) in

  -- Move the prepared register x into regB if c = 0
  let (c,x,regB) = (force moveBlock @ n) (c, x, regB) in

  -- Control Modular Step Function
  let cModMultStep = lift forall step. \((c,qs,regA,regB,regMod),q) :: ((Qubit, List [_<step] Qubit, List[_<n+1] Qubit, List[_<n+1] Qubit, List[_<n+1] Bit), Qubit).
    -- Prepare the qubits register from classic register
    let (regMod, regQ) = (force qinitFromBits @ n) regMod in

    -- First toffoli on regA's k-th bit
    let (c,q,regA) = (force bitWiseToffoli @ n @ step) (c, q, regA) in 

    -- Inverse Modular Adder 
    let (regA,regB,regQ) = (force iModAdder @ n) (regA, regB, regQ) in

    -- Discard regQ 
    let _ = (force qdiscardMany @ n) regQ in

    -- Second toffoli on regA's k-th bit
    let (c,q,regA) = (force bitWiseToffoli @ n @ step) (c, q, regA) in 

    (c,qs:q,regA,regB,regMod) in

  -- Fold loop
  let (c,x,regA,regB,regMod) = fold(cModMultStep, (c,[],regA,regB,regMod), x) in
  -- discard regA
  let _ = (force qdiscardMany @ n) regA in
  -- Return 
  (c, x, regB, regMod)
