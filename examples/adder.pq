{-
  Basic quantum arithmetic operations.
  from Vlatko Vedral, Adriano Barenco and Artur Ekert. Quantum Networks for Elementary Arithmetic Operations. Physical Review A, 54(2):147-153, 1996.
  This implementation of quantum arithmetic is by no means state-of-the-art, but it employs ancillary qubits
  to perform the operations, so its analysis is interesting.
-}

--- Utils --- 

-- reverses a list of i qubits
rev = forall n. forall d. \list::List[_<n] Qubit{d}.
  let revStep = lift forall step.\(qs, q)::(List[_<step] Qubit{d}, Qubit{d}). qs:q
  in fold(revStep, [], list)

-- reverses a list of i pairs of qubits
revpair = forall n. forall d. \list::List[_<n] (Qubit{d},Qubit{d}).
  let revStep = lift forall step.\(qs, q)::(List[_<step] (Qubit{d},Qubit{d}), (Qubit{d},Qubit{d})). qs:q
  in fold(revStep, [], list)

-- zips two lists of i qubits
qzip = forall n . forall d. \(a,b) :: (List[_<n+1] Qubit{d}, List[_<n+1] Qubit{d}).
  let qzipStep = lift forall step. \((llist,reslist),relem) :: ((List[_<(n+1)-step] Qubit{d}, List[_<step] (Qubit{d},Qubit{d})), Qubit{d}).
    let ls:lelem = (llist !:: List[_<(n-step)+1] Qubit{d}) in -- we can assume this because zipstep is only called by fold, where step < n+1
    let reslist = reslist : (lelem, relem) in
    (ls, reslist)
  in let (_, zippedlist) = (fold(qzipStep, (a,[]), b) :: (List[_<0] Qubit{d}, List[_<n+1] (Qubit{d},Qubit{d})))
  in zippedlist

-- unzips a list of i pairs of qubits
qunzip = forall n . forall d. \a :: List[_<n] (Qubit{d},Qubit{d}).
  let qunzipStep = lift forall step. \((leftList, rightList), pair) :: ((List[_<step] Qubit{d}, List[_<step] Qubit{d}), (Qubit{d},Qubit{d})).
    let (a,b) = pair in
    (leftList:a, rightList:b)
  in fold(qunzipStep, ([],[]), (force revpair @ n @ d) a)

interleave = forall n . forall d. \a :: List[_<n] (Qubit{d},Qubit{d}). 
  let interleaveStep = lift forall step . \(reslist, pair) :: (List[_<step] ((Qubit{d},Qubit{d}),Qubit{d}), (Qubit{d},Qubit{d})).
    let c = apply(QInit0,()) in reslist:(pair,c)
  in fold(interleaveStep, [], (force revpair @ n @ d) a)

--- short-hands ---
-- We do not care about local metrics, so we preemptively instantiate them to 0

{-
qnot = (force qnot @0)
cnot = (force cnot @0@0)
toffoli = (force toffoli @0@0@0)
qdiscard = (force qdiscard @0)
-}


--- Adder Utils ---

-- CARRY (Fig. 3.i)
carry :: ![0](forall[0,0] d. (Qubit{d}, Qubit{d}, Qubit{d}, Qubit{d}) -o[4, 0] (Qubit{d+5}, Qubit{d+4}, Qubit{d+5}, Qubit{d+5}))
carry d (c, a, b, cnext) =
  let (a, b, cnext) = (force toffoli @d+2 @d @d) a b cnext in
  let (a,b) = (force cnot @d+3 @d+3) a b in
  let (c, b, cnext) = (force toffoli @d @d+4 @d+3) c b cnext in
  (c, a, b, cnext)

-- REVERSE CARRY
icarry :: ![0](forall[0,0] d. (Qubit{d}, Qubit{d}, Qubit{d}, Qubit{d}) -o[4, 0] (Qubit{d+3}, Qubit{d+5}, Qubit{d+5}, Qubit{d+5}))
icarry d (c, a, b, cnext) =
  let (c, b, cnext) = (force toffoli @d+2 @d @d) c b cnext in
  let (a,b) = (force cnot @d+3 @d+3) a b in
  let (a, b, cnext) = (force toffoli @d+4 @d+4 @d+3) a b cnext in
  (c, a, b, cnext)

-- SUM (Fig. 3.ii)
csum :: ![0](forall[0,0] d. (Qubit{d}, Qubit{d}, Qubit{d}) -o[3, 0] (Qubit{d+2}, Qubit{d+1}, Qubit{d+2}))
csum d (c, a, b) =
  let (a,b) = (force cnot @d @d) a b in
  let (c,b) = (force cnot @d @d+1) c b in
  (c, a, b)

--- Adder subroutines ---
-- (Fig. 2, first half)
adderFirstPhase :: ![0](forall[0,0] n. forall[0,0] d. (List[_ < n + 1] Qubit{d}, List[_ < n + 1] Qubit{d}, Qubit{d}) -o[1 + (n + 1) * 3 + 1, 0] (List[_ < (n + 1) - 1 + 1] ((Qubit{d}, Qubit{d}), Qubit{d}), Qubit{d}))
adderFirstPhase n d (a, b, overflow) =
  let ab = (force qzip @ n @ d) (a,b) in
  let abc = (force interleave @ n+1 @ d) ab in --every first position is a, every second is b, every third is c
  let initialAcc = apply(QInit0,()) in
  
  -- Fix the n_b+1 last qubit
  let rest:((a,b),c) = abc in
  let _ = (force qdiscard @d) c in
  let abc = rest:((a,b),overflow) in

  let adderStepFirst = lift forall step . \((reslist, c), ((a,b),cnext)) :: ((List[_<step] ((Qubit{d},Qubit{d+5}),Qubit{d+4}), Qubit{d+5}), ((Qubit{d},Qubit{d}),Qubit{d})) .
    let (c, a, b, cnext) = (force carry @d) (c, a, b, cnext) in
    (reslist : ((c, a), b), cnext) in
  let (reslist,overflow) = fold(adderStepFirst, ([], initialAcc), abc) in
  (reslist,overflow) -- note that the output triples are reversed

adderSecondPhase :: ![0](forall[0,0] n. forall[0,0] d. (Qubit{d}, List[_<n] ((Qubit{d}, Qubit{d}), Qubit{d})) -o[3*n + 1, 0] (Qubit{d}, List[_<n] (Qubit{d}, Qubit{d})))
adderSecondPhase n d (cfirst, abc) =
  --subcircuit used in the second phase: carry followed by sum, carry discarded:
  let csum = lift \(c,a,b,cnext) :: (Qubit{d},Qubit{d},Qubit{d},Qubit{d}). 
      let (c,a,b,cnext) = (force icarry @d) (c,a,b,cnext) in
      let (c,a,b) = (force csum @d) (c,a,b) in
      let _ = (force qdiscard @d) cnext in
      (c,a,b) in
  let boxedSum = box csum in
  --step function:
  let adderStepSecond = lift $ forall step. \((cnext, reslist),((c,a),b)) :: ((Qubit{d}, (List[_<step] (Qubit{d},Qubit{d}))),((Qubit{d},Qubit{d}),Qubit{d})).
    let (c,a,b,cnext) = apply(boxedSum, (c,a,b,cnext)) in 
    (c, reslist:(a,b))
  in fold(adderStepSecond, (cfirst,[]), abc)

--- Adder ---
adder :: ![0](forall[0,0] n. forall[0,0] d. (List[_<n+1] Qubit{d}, List[_<n+1] Qubit{d}, Qubit{d}) -o[1 + (n + 1) * 3 + 1, 0] (List[_<n+1] Qubit{d}, List[_<n+1] Qubit{d}, Qubit{d}))
adder n d (a, b, overflow) =
  let (rest:((c,a),b),overflow) = (force adderFirstPhase @ n @ d) (a,b,overflow) in
  let (a,b) = (force cnot @d @d) a b in
  let (c,a,b) = (force csum @d) (c,a,b) in
  let (lastc, final) = (force adderSecondPhase @ n @ d) (c, rest) in
  let _ = (force qdiscard @ d) lastc in
  let complete = (((force revpair @ n @ d) final) : (a,b)) in --add the first block back in
  let (ares,b) = (force qunzip @ n+1 @ d) complete in --separate a and b
  ((force rev @ n+1 @ d) ares, (force rev @ n+1 @ d) b, overflow) --rearrange the bits in the right order
