Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Bool.Bool.
Require Import Setoid.


Module MyList.

Inductive list (A: Type) :=
  | nil
  | cons (x: A) (l: list A).

(* The following two lines mark the type argument "A" implicit in nil and cons.
  I.e., we ask Coq to insert and infer the types wherever necessary. *)
Arguments nil {A}.
Arguments cons {A}.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


Fixpoint app {A: Type} (l1: list A) (l2: list A) : list A :=
  match l1 with
  | [] => l2
  | x :: l1' => x :: (app l1' l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Fixpoint rev {A: Type} (l: list A) : list A :=
  match l with
  | [] => []
  | x :: l' => rev l' ++ [x]
  end.

Theorem app_assoc : forall {A: Type} (l1: list A) (l2: list A) (l3 : list A),
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros. induction l1 as [|l'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1. reflexivity.
Qed.

Lemma app_nil_r: forall {A: Type} (l: list A),
  l ++ [] = l.
Proof.
  intros.
  induction l as [|l'].
  - simpl. reflexivity.
  - simpl. rewrite IHl. reflexivity.
Qed.

Lemma rev_distr: forall {A: Type} (l1: list A) (l2: list A),
  rev(l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros.
  induction l1 as [|l1'].
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHl1. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive: forall {A: Type} (l: list A),
  rev (rev l) = l.
Proof.
  intros.
  induction l as [|l'].
  - simpl. reflexivity.
  - simpl. rewrite rev_distr. rewrite IHl. simpl. reflexivity.
Qed.


(* bring "&&" notation into scope *)
Local Open Scope bool_scope. 

Fixpoint eqb_list {A: Type} (eqb: A -> A -> bool) (l1: list A) (l2: list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | x :: l1', y :: l2' => 
    eqb x y && eqb_list eqb l1' l2'
  | _, _ => false
  end.

Search(_ && _ = true).

Search(_, _ -> _).

Theorem eqb_list_sound: 
  forall {A: Type} (eqb: A -> A -> bool) l1 l2,
    (* assume the equality function for the element type is sound *)
    (forall x y, eqb x y = true -> x = y) ->
    (* show that the list equality is sound *)
    eqb_list eqb l1 l2 = true -> l1 = l2.
Proof.
  intros A eqb l1.
  induction l1 as [|x1 l1].
  - destruct l2.
    + reflexivity.
    + simpl. discriminate.
  - destruct l2 as [|x2 l2'].
    + discriminate.
    + simpl. intros H. rewrite andb_true_iff. intros H0. destruct H0.
      apply H in H0. apply IHl1 in H1.
      * rewrite H0. rewrite H1. reflexivity.
      * apply H.
Qed.

(* Theorem eqb_list_sound: 
  forall {A: Type} (eqb: A -> A -> bool) l1 l2,
    (* assume the equality function for the element type is sound *)
    (forall x y, eqb x y = true -> x = y) ->
    (* show that the list equality is sound *)
    eqb_list eqb l1 l2 = true -> l1 = l2.
Proof.
  intros.
  induction l1 as [|x1 l1' IHl1].
  - destruct l2 as [|x2 l2'].
    + reflexivity.
    + discriminate.
  - destruct l2 as [|x2 l2'].
    + discriminate.
    +  *)

End MyList.



Module BinaryTree.

Inductive tree (A: Type) := 
  | leaf
  | node (a: A) (l: tree A) (r: tree A).

Arguments leaf {A}.
Arguments node {A}.

Fixpoint flip {A: Type} (t: tree A) : tree A :=
  match t with
  | leaf => t
  | node x l r =>
    node x (flip r) (flip l)
  end.

Theorem flip_involutive: forall {A: Type} (t: tree A),
  flip (flip t) = t.
Proof.
  intros.
  induction t.
  - reflexivity.
  - simpl. rewrite IHt1. rewrite IHt2. reflexivity.
Qed.

End BinaryTree.



Module BTree.

Inductive btree (A: Type) :=
  | leaf
  | node (a: A) (ls: list (btree A)).

Arguments leaf {A}.
Arguments node {A}.

Fixpoint flip {A: Type} (t: btree A) : btree A :=
  match t with
  | leaf => t
  | node x ls =>
    (* flip each subtree, then reverse the list *)
    (* [map] and [rev] are defined in the standard library:
      https://coq.inria.fr/doc/master/stdlib/Coq.Lists.List.html
      *)
    node x (rev (map flip ls))
  end.
(* Search rev map. *)

(* map_rev: forall [A B : Type] (f : A -> B) (l : list A), map f (rev l) = rev (map f l) *)

(* Search rev. *)

(* Search map. *)

(* Note: we haven't seen enough Coq to be able to prove this, but you should 
  at least try the proof, observe where things get stuck, and form your 
  hypothesis as to why the proof is stuck *)

Lemma map_flip_involutive: forall {A: Type} (ls: list (btree A)),
  map flip(map flip ls) = ls.
Proof.
  intros.
  induction ls as [|ls'].
  - reflexivity.
  - simpl. (* Cyclic dependency of flip (flip t). If we don't use this lemma and directly write this induction in the flip_involutive, same problem occurs. *)
  Abort.

Theorem flip_involutive: forall {A: Type} (t: btree A),
  flip (flip t) = t.
Proof.
  intros.
  induction t.
  - reflexivity.
  - simpl. rewrite map_rev. rewrite rev_involutive. rewrite map_flip_involutive. reflexivity.
  (* destruct t.
  - reflexivity.
  - simpl. rewrite map_rev. rewrite rev_involutive.
    induction ls as [|ls'].
    + reflexivity.
    + simpl. *)
    (* We cannot rewrite *)
    Abort.

End BTree.




Module TotalMap.

(* same as the id type in the PartialMap module in SF's Lists chapter *)
Inductive id : Type :=
  | Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

(* A total map from keys of type id to values of type A can be represented
   as a function from id to A *)
Definition total (A: Type) : Type := id -> A.

Check total nat.

(* Try defining the following function. If it's definable, prove that it is sound. If not, explain why you can't define it. *)
Definition eqb_total {A: Type} (eqb: A -> A -> bool) (m1: total A) (m2: total A) : bool :=
  match m1, m2 with
  | (id1 -> A), (id2 -> A) => eqb_id(id1, id2)
(* I am not sure we can do pattern matching on m1 or m2. Since total just defines a mapping between a key of type id and a value of type A, the possible pairs can be infinite unless otherwise specified. Since a finite set or a inductive definition is not given, we cannot define this function. *)
  end.


Theorem eqb_total_sound: 
  forall {A: Type} (eqb: A -> A -> bool) m1 m2,
    (* assume the equality function for the element type is sound *)
    (forall x y, eqb x y = true -> x = y) ->
    (* show that the map equality is sound *)
    eqb_total eqb m1 m2 = true -> m1 = m2.
Proof.
  intros.
  Abort.

End TotalMap.