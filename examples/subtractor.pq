{-
  Basic quantum arithmetic operations.
  from Vlatko Vedral, Adriano Barenco and Artur Ekert. Quantum Networks for Elementary Arithmetic Operations. Physical Review A, 54(2):147-153, 1996.
  This implementation of quantum arithmetic is by no means state-of-the-art, but it employs ancillary qubits
  to perform the operations, so its analysis is interesting.
-}

--- list functions ---

-- reverses a list of i qubits
rev = forall n. forall d. \list::List[_<n] Qubit{d}.
  let revStep = lift forall step.\(qs, q)::(List[_<step] Qubit{d}, Qubit{d}). qs:q
  in fold(revStep, [], list)

-- reverses a list of i pairs of qubits
revpair = forall n. forall d. \list::List[_<n] (Qubit{d},Qubit{d}).
  let revStep = lift forall step.\(qs, q)::(List[_<step] (Qubit{d},Qubit{d}), (Qubit{d},Qubit{d})). qs:q
  in fold(revStep, [], list)

-- reverses a list of i triplets of qubits
revtriplets = forall n. forall d. \list::List[_<n] ((Qubit{d},Qubit{d}),Qubit{d}).
  let revStep = lift forall step.\(qs, q)::(List[_<step] ((Qubit{d},Qubit{d}),Qubit{d}), ((Qubit{d},Qubit{d}),Qubit{d})). qs:q
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

-- adds a qubits in front a list of n pairs of qubits
interleave = forall n . forall d. \a :: List[_<n] (Qubit{d},Qubit{d}). 
  let interleaveStep = lift forall step . \(reslist, pair) :: (List[_<step] ((Qubit{d},Qubit{d}),Qubit{d}), (Qubit{d},Qubit{d})).
    let c = force qinit0 in reslist:(pair,c)
  in fold(interleaveStep, [], (force revpair @ n @ d) a)


--- Adder Utils ---

-- CARRY (Fig. 3.i)
carry :: ![0](forall[0,0] d. (Qubit{d}, Qubit{d}, Qubit{d}, Qubit{d}) -o[4, 0] (Qubit{d+5}, Qubit{d+4}, Qubit{d+5}, Qubit{d+5}))
carry d (c, a, b, cnext) =
  let (a, b, cnext) = (force toffoli @d @d @d) a b cnext in
  let (a,b) = (force cnot @d+3 @d+3) a b in
  let (c, b, cnext) = (force toffoli @d @d+4 @d+3) c b cnext in
  (c, a, b, cnext)

-- REVERSE CARRY
icarry :: ![0](forall[0,0] d. (Qubit{d}, Qubit{d}, Qubit{d}, Qubit{d}) -o[4, 0] (Qubit{d+3}, Qubit{d+5}, Qubit{d+5}, Qubit{d+5}))
icarry d (c, a, b, cnext) =
  let (c, b, cnext) = (force toffoli @d @d @d) c b cnext in
  let (a,b) = (force cnot @d+3 @d+3) a b in
  let (a, b, cnext) = (force toffoli @d+4 @d+4 @d+3) a b cnext in
  (c, a, b, cnext)

-- SUM (Fig. 3.ii)
csum :: ![0](forall[0,0] d. (Qubit{d}, Qubit{d}, Qubit{d}) -o[3, 0] (Qubit{d+1}, Qubit{d+2}, Qubit{d+2}))
csum d (c, a, b) =
  let (c,b) = (force cnot @d @d) c b in
  let (a,b) = (force cnot @d @d+1) a b in
  (c, a, b)

-- First part
subtractorFirstPhase :: ![0](forall[0,0] n. forall[0,0] d. List[_<n] (Qubit{d}, Qubit{d}) -o[3*n+1, 0] (List[i<n] ((Qubit{d + (i + 1) * 7},Qubit{d + (i + 1) * 7}),Qubit{d + (i + 1) * 7}),Qubit{d + n * 7}))
subtractorFirstPhase n d ab =
  -- every first position is a, every second is b, every third is c
  let abc = (force interleave @ n @ d) ab in 
  -- insert c_0 in front of the list of 3-tuple 
  let initialAcc = (force qinit0) in
  
  --step function:
  let subtractorStepFirst = lift $ forall step. \((reslist,cnext),((c,a),b)) :: (((List[i<step] ((Qubit{d+(i+1)*7},Qubit{d+(i+1)*7}),Qubit{d+(i+1)*7})),Qubit{d+step*7}),((Qubit{d},Qubit{d}),Qubit{d})).
    let (c,a,b) = (force csum @ d+(step*7)) (c,a,b) in
    let (c,a,b,cnext) = (force carry @ d+(step*7)+2) (c,a,b,cnext) in -- opposite icarry == carry
    (reslist:((c,a),b),cnext)
  in fold(subtractorStepFirst, ([],initialAcc), (force revtriplets @ n @ d) abc) -- since the stepfunc will reverse the list we premtivily reverse it

-- Second part
subtractorSecondPhase :: ![0](forall[0,0] n. forall[0,0] d. (List[_<n] ((Qubit{d},Qubit{d}),Qubit{d}),Qubit{d}) -o[3*n+1, 0] (List[i<n] (Qubit{d+((i+1)*5)}, Qubit{d+((i+1)*5)}), Qubit{d+(n*5)}))
subtractorSecondPhase n d (list, clast) =
  let subtractorStepSecond = lift forall step . \((reslist, c), ((a,b),cnext)) :: ((List[i<step] (Qubit{d+((i+1)*5)},Qubit{d+((i+1)*5)}), Qubit{d+(step*5)}), ((Qubit{d},Qubit{d}),Qubit{d})) .
    let (c, a, b, cnext) = (force icarry @d+(step*5)) (c, a, b, cnext) in
    let _ = (force qdiscard @ d+step*5+5) cnext in
    (reslist:(a,b),c) in
  let (reslist,cfirst) = fold(subtractorStepSecond, ([],clast), list) in
  (reslist,cfirst) -- note that the output triples are reversed

-- Subtractor
subtractor :: ![0](forall[0,0] n. forall[0,0] d. (List[_<n+1] Qubit{d}, List[_<n+1] Qubit{d}, Qubit{d}) -o[3*(n+1) + 1, 0] (List[_<n+1] Qubit{d + 12 * n + 17}, List[_<n+1] Qubit{d + 12 * n + 17}, Qubit{d + 7 * n + 8}))
subtractor n d (a, b, overflow) =
  -- first part
  let ab = (force qzip @n @d) (a,b) in
  -- this operation will be done n times (on list_n+1) so we save up the last pair (a,b) then single handedly manage it
  let ab:(alast,blast) = ab in
  let (list,clast) = (force subtractorFirstPhase @n @d) ab in
  
  -- bottom of the valley, individually handle
  let (clast,alast,blast) = (force csum @ d + n * 7) (clast,alast,blast) in
  let (alast,blast) = (force cnot @ d + n * 7 + 2 @ d + n * 7 + 2) alast blast in
  let (clast,alast,blast,overflow) = (force icarry @ d + n * 7 + 3) (clast,alast,blast,overflow) in

  -- final part: carry operation and discard of c qubits
  -- input: list_n+1 triplets + overflow
  -- output: list_n+1 pairs + overflow
  let (list,cfirst) = (force subtractorSecondPhase @ n @ d + (n + 1) * 7) ((force revtriplets @ n @ d + (n + 1) * 7) list, clast) in

  -- discard the last carry qubit 
  let _ = (force qdiscard @ d + 12 * n + 7) cfirst in
  -- reassemble the last pair into the list
  let list = list:(alast,blast) in
  -- parsing of the qubits
  let (a,b) = (force qunzip @ n+1 @ d + 12 * n + 17) list in --separate a and b
  ((force rev @ n+1 @ d + 12 * n + 17) a, (force rev @ n+1 @ d + 12 * n + 17) b, overflow) --rearrange the bits in the right order

-- This is the single gate invese subroutine of the adder subroutine
