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

-- reverses a list of i triplets of qubits
revtriplets = forall n. forall d. \list::List[_<n+1] ((Qubit{d},Qubit{d}),Qubit{d}).
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
csum :: ![0](forall[0,0] d. (Qubit{d}, Qubit{d}, Qubit{d}) -o[3, 0] (Qubit{d+2}, Qubit{d+1}, Qubit{d+2}))
csum d (c, a, b) =
  let (a,b) = (force cnot @d @d) a b in
  let (c,b) = (force cnot @d @d+1) c b in
  (c, a, b)

--- Adder subroutines ---
-- (Fig. 2, first half)
adderFirstPhase :: ![0](forall[0,0] n. forall[0,0] d. (List[_ < n + 1] Qubit{d}, List[_ < n + 1] Qubit{d}, Qubit{d}) -o[3*(n + 1) + 1, 0] (List[_ < n + 1] ((Qubit{d + (n + 1 + 1) * 5}, Qubit{d + (n + 1 + 1) * 5}), Qubit{d + (n + 1 + 1) * 5}), Qubit{d + (n + 1 + 1) * 5}))
adderFirstPhase n d (a, b, overflow) =
  let ab = (force qzip @ n @ d) (a,b) in
  let reslist:(a,b) = ab in
  let reslist = (force interleave @ n @ d) reslist in --every first position is a, every second is b, every third is c
  let abc = reslist:((a,b),overflow) in
  let cfirst = force qinit0 in
  
  let adderStepFirst = lift forall step . \((reslist, c), ((a,b),cnext)) :: ((List[i<step] ((Qubit{d+((i+1)*5)},Qubit{d+((i+1)*5)}),Qubit{d+((i+1)*5)}), Qubit{d+(step*5)}), ((Qubit{d},Qubit{d}),Qubit{d})) . 
    let (c, a, b, cnext) = (force carry @d+(step*5)) (c, a, b, cnext) in
    (reslist : ((c, a), b), cnext) in 
  let (reslist,overflow) = fold(adderStepFirst, ([], cfirst), abc) in
  ((force revtriplets @n @d+((n+2)*5)) (reslist :: List[i<n+1] ((Qubit{d+((n+2)*5)},Qubit{d+((n+2)*5)}),Qubit{d+((n+2)*5)})), overflow) -- note that the output triples are reversed so return them in the right order 

adderSecondPhase :: ![0](forall[0,0] n. forall[0,0] d. (Qubit{d}, List[_<n] ((Qubit{d}, Qubit{d}), Qubit{d})) -o[3*n + 1, 0] (Qubit{d+n*7}, List[i<n] (Qubit{d+(i+1)*7}, Qubit{d+(i+1)*7})))
adderSecondPhase n d (cfirst, abc) =
  --step function:
  let adderStepSecond = lift $ forall step. \((cnext, reslist),((c,a),b)) :: ((Qubit{d+step*7}, (List[i<step] (Qubit{d+((i+1)*7)},Qubit{d+((i+1)*7)}))),((Qubit{d},Qubit{d}),Qubit{d})).
      let (c,a,b,cnext) = (force icarry @d+(step*7)) (c,a,b,cnext) in
      let (c,a,b) = (force csum @d+(step*7)+5) (c,a,b) in
      let _ = (force qdiscard @d+(step*7)+5) cnext in
      (c, reslist:(a,b)) 
  in fold(adderStepSecond, (cfirst,[]), abc)

--- Adder ---
adder :: ![0](forall[0,0] n. forall[0,0] d. (List[_<n+1] Qubit{d}, List[_<n+1] Qubit{d}, Qubit{d}) -o[3*(n+1) + 1, 0] (List[_<n+1] Qubit{12*n + 20 + d}, List[_<n+1] Qubit{12*n + 20 + d}, Qubit{d + (n+2) * 5}))
adder n d (a, b, overflow) =
  let (rest:((c,a),b),overflow) = (force adderFirstPhase @ n @ d) (a,b,overflow) in
  let (a,b) = (force cnot @d+(n+2)*5 @d+(n+2)*5) a b in
  let (c,a,b) = (force csum @1+d+(n+2)*5) (c,a,b) in
  let (lastc, final) = (force adderSecondPhase @ n @3+d+(n+2)*5) (c, rest) in
  let _ = (force qdiscard @ 12*n + 13 + d) lastc in
  let complete = (((force revpair @ n @ 12*n + 20 + d) final) : (a,b)) in --add the first block back in
  let (a,b) = (force qunzip @ n+1 @ 12*n + 20 + d) complete in --separate a and b
  ((force rev @ n+1 @ 12*n + 20 + d) a, (force rev @ n+1 @ 12*n + 20 + d) b, overflow) --rearrange the bits in the right order
