{- 
Bell state
-}

bell :: ![0](forall[0,0] dq. forall[0,0] dp.
  (Qubit{dq}, Qubit{dp}) -o[0,0] (Qubit{max(dq, dp)}, Qubit{max(dq, dp)}))
bell dq dp (q, p) = 
    let q = (force hadamard @dq) q in
    let (q,p) = (force cnot @dq @dp) q p in
    (q,p)

teleport :: ![0](forall[0,0] dr. (Qubit{dr}, Qubit{dr+6}))
teleport dr = 
    let q = force qinit0 in
    let p = force qinit0 in
    let (q,p) = (force bell @0 @0) (q,p) in (q,p) 
