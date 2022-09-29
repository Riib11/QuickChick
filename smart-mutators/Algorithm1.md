# Smart Mutators Algorithm (v1)

The inductive datatype to mutate over has the form

```coq
Inductive <Dat> :=
  i@[ | <DatCon i> : j@[ <DatConPrmTyp i,j> ] -> <Dat> ]
```

The inductive relation to mutate with respect to has the form

```coq
Inductive <Rel> : i@[ <RelPrmType i> : Set ] -> <Dat> -> Prop :=
  j@[ | <RelCon j> : 
          -- constructor parameters
          k@[ <RelConPrm j,k> : <RelConPrmTyp j,k> ] ->
          -- constructor non-inductive hypotheses
          l@[ <RelConHyp i,l> ] ->
          -- inductive hypotheses
          <Rel> i@[ <RelConIndHypArg i,j> ] <RelConIndHypArgDat j> ->
          -- constructor output
          <Rel> i@[ <RelConArg i,j> ] <RelConArgDat j>      
    ]
```

Then, the mutation algorithm is the following:

```coq
mut i@[ <RelPrm i> : <RelPrmType i> ] (x: <Dat>): option (G <Dat>) :=
  let n := size x in
  let mut_here: G (option <Dat>) :=
        arbitrarySizeST (fun x => <Rel> i@[ <RelPrm i> ] x) n in
  match x with
  j@[
    <RelCon j> k@[ <RelConArg j,k> ] =>
      backtrack
        [ (1, mut_herre)

        ] 
  ]
```