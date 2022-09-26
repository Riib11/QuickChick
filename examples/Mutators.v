From QuickChick Require Import QuickChick.

Require Import List. Import ListNotations.
Require Import String. Open Scope string.

Inductive Tree :=
| Leaf : Tree
| Node : nat -> Tree -> Tree -> Tree.

Derive (Arbitrary, Show, Sized) for Tree. 

Inductive bst : nat -> nat -> Tree -> Prop :=
| bst_leaf : forall lo hi, bst lo hi Leaf
| bst_node : forall lo hi x l r,
    le (S lo) x ->  le (S x) hi ->
    bst lo x l -> bst x hi r ->
    bst lo hi (Node x l r).

Derive DecOpt for (le x y).

Derive ArbitrarySizedSuchThat for (fun x => le y x).
Derive ArbitrarySizedSuchThat for (fun t => bst lo hi t).

Derive DecOpt for (bst lo hi t).

Fixpoint is_bst (lo hi : nat) (t : Tree) :=
  match t with
  | Leaf => true
  | Node x l r =>
    andb ((lo < x /\ x < hi) ?)
         (andb (is_bst lo x l)
               (is_bst x hi r))
  end.

Check @arbitraryST.

Fixpoint mut_bst (lo hi: nat) (t: Tree) : G (option Tree) :=
  match t return G (option Tree) with
  | Leaf => ret (Some Leaf)
  | Node x l r =>
    bind (freq_ (ret true) [(1, ret true); (size t, ret false)]) (fun b =>
      if b: bool then
        (* mut here *)
        @arbitraryST _ (fun t => bst lo hi t) _
      else
        (* mut in branch, weighted by size *)
        freq_ (ret (Some t)) 
          [ ( size l 
            , bind (mut_bst lo x l) 
              ( fun opt_l' => 
                match opt_l' return G (option Tree) with
                | Some l' => ret (Some (Node x l' r))
                | None => ret None
                end
              ))
          ; ( size l 
            , bind (mut_bst x hi r) 
              ( fun opt_r' => 
                match opt_r' return G (option Tree) with
                | Some r' => ret (Some (Node x l r'))
                | None => ret None
                end
              )) ]
    )
  end.

Definition t1: Tree :=
  Node 4
    (Node 2
      (Node 1 Leaf Leaf)
      (Node 3 Leaf Leaf))
    (Node 6
      (Node 5 Leaf Leaf)
      (Node 7 Leaf Leaf)).

Check @arbitraryST.

Program Definition mut_preserves_bst (lo hi: nat): G bool :=
  bind (@arbitraryST _ (fun t => bst lo hi t) _) (fun opt_t =>
  match opt_t: option Tree return G bool with
  | None => ret true
  | Some t =>
    bind (mut_bst lo hi t) (fun opt_t' =>
      match opt_t': option Tree return G bool with
      | None => ret true
      | Some t' => ret (is_bst lo hi t')
      end)
  end).

QuickChick mut_preserves_bst.

(* TODO: not sure why this doesn't work... *)
(* Program Definition mut_preserves_bst_prop :=
  forAll (arbitrary: G nat) (fun lo =>
  forAllMaybe (genST (fun hi => le lo hi)) (fun hi =>
  forAllMaybe (genST (fun t => bst lo hi t)) (fun t =>
  forAllMaybe (mut_bst lo hi t) (fun t' => 
  _)))).
 *)
