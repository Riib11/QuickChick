From QuickChick Require Import QuickChick.

Require Import List. Import ListNotations.
Require Import String. Open Scope string.

Inductive Tree :=
| Leaf : Tree
| Node : nat -> Tree -> Tree -> Tree.

Derive (Arbitrary, Show) for Tree. 

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

Fixpoint insert (x : nat) (t : Tree) :=
  match t with
  | Leaf => Node x Leaf Leaf
  | Node y l r =>
    if x < y ? then
      Node y (insert x l) r
    else if x > y ? then
      Node y l (insert x r)
    else t
  end.

Definition insert_preserves_bst (x : nat) (t : Tree) :=
  if is_bst 0 10 t then
    is_bst 0 10 (insert x t)
  else true.

Theorem insert_preserves_bst_prop :
  forall (x : nat) (t : Tree),
    bst 0 10 t -> bst 0 10 t.
Proof.
  intros x t pf.
  apply pf.
Qed.


(* Definition bst_checker_prop :=
  forAllMaybe (genST (fun t => bst 0 17 t)) (fun t => 
  forAll (choose (1, 16)) (fun x => 
  bst 0 17 (insert x t))).  *)
(*  is_bst 0 17 (insert x t))). *)

(* Extract Constant defNumTests => "20000". *)
(* QuickChick bst_checker_prop.  *)



