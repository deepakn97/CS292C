(** Potentially unknown boolean *)
Inductive ubool : Type :=
  | T (* true *)
  | U (* unknown *)
  | F (* false *)
  .

(** Negation *)
Definition negu (u: ubool) : ubool :=
  match u with
  | T => F
  | U => U
  | F => T
  end.
  
(** Conjunction *)
Definition andu (u1: ubool) (u2: ubool) : ubool := 
  match u1 with
  | T => u2
  | U => match u2 with
    | F => F
    | _ => U
    end
  | F => F
  end.
  
(** Disjunction *)
Definition oru (u1: ubool) (u2: ubool) : ubool :=
  match u1 with
  | T => T
  | U => match u2 with
    | T => T
    | _ => U
    end
  | F => u2
  end.
  
Notation "x && y" := (andu x y).
Notation "x || y" := (oru x y).
Notation "- x" := (negu x).

Theorem negu_negu: forall u, - - u = u.
Proof. 
  destruct u.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem andu_self: forall u, u && u = u.
Proof.
  destruct u.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem de_morgan_andu: forall u1 u2, - (u1 && u2) = - u1 || - u2.
Proof.
  intros.
  destruct u1 eqn:Eu1.
  - simpl. reflexivity.
  - simpl. destruct u2 eqn:Eu2. simpl. reflexivity. simpl. reflexivity. simpl. reflexivity.
  - simpl. reflexivity.
Qed. 

Theorem andu_comm: forall u1 u2, u1 && u2 = u2 && u1.
Proof.
  intros.
  destruct u1 eqn:Eu1.
  - simpl. destruct u2. 
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. destruct u2. 
    + reflexivity.
    + reflexivity.
    + reflexivity.
Qed.

Theorem andu_assoc: forall u1 u2 u3, u1 && (u2 && u3) = u1 && u2 && u3.
Proof.
  intros.
  destruct u1 eqn:Eu1.
  - simpl. reflexivity.
  - simpl. destruct u2 eqn: Eu2.
    + simpl. reflexivity.
    + simpl. destruct u3. 
      * reflexivity.
      * reflexivity.
      * reflexivity.
    + simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem oru_self: forall u, u || u = u.
Proof.
  intros.
  destruct u eqn:Eu.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem andu_distr_oru: forall u1 u2 u3, u1 && (u2 || u3) = u1 && u2 || u1 && u3.
Proof.
  intros.
  destruct u1 eqn:Eu1.
  - simpl. reflexivity. 
  - simpl. destruct u2 eqn:Eu2.
    + simpl. destruct u3 eqn:Eu3.
      * simpl. reflexivity.
      * simpl. reflexivity.
      * simpl. reflexivity.
    + simpl. destruct u3 eqn:Eu3.
      * simpl. reflexivity.
      * simpl. reflexivity.
      * simpl. reflexivity.
    + simpl. reflexivity. 
  - simpl. reflexivity. 
Qed.


(** For the following theorems, do NOT use destruct to perform case analysis. *)
Module NoDestruct.

Theorem de_morgan_oru: forall u1 u2, - (u1 || u2) = -u1 && -u2.
Proof.
  intros.
  rewrite <- negu_negu with (u := -u1 && -u2).
  rewrite de_morgan_andu with (u1 := - u1) (u2 := - u2).
  rewrite negu_negu. rewrite negu_negu.
  reflexivity. 
Qed.

Theorem oru_self: forall u, u || u = u.
Proof.
  intros.
  rewrite <- negu_negu with (u := u || u). 
  rewrite de_morgan_oru. 
  rewrite andu_self.
  rewrite negu_negu.
  reflexivity.
Qed.

Theorem oru_comm: forall u1 u2, u1 || u2 = u2 || u1.
Proof.
  intros.
  rewrite <- negu_negu with (u := u1 || u2).
  rewrite de_morgan_oru. rewrite andu_comm with (u1 := -u1) (u2:= -u2).
  rewrite de_morgan_andu.
  rewrite negu_negu. rewrite negu_negu. 
  reflexivity.
Qed.

Theorem oru_assoc: forall u1 u2 u3, u1 || (u2 || u3) = u1 || u2 || u3.
Proof.
  intros.
  rewrite <- negu_negu with (u := u1 || (u2 || u3)).
  rewrite de_morgan_oru.
  rewrite de_morgan_oru with (u1 := u2) (u2 := u3).
  rewrite andu_assoc with (u1 := -u1) (u2 := -u2) (u3 := -u3).
  rewrite <- de_morgan_oru. 
  rewrite de_morgan_andu with (u1 := - (u1 || u2)) (u2 := -u3).
  rewrite negu_negu. rewrite negu_negu.
  reflexivity.
Qed.

Theorem oru_distr_andu: forall u1 u2 u3, u1 || (u2 && u3) = (u1 || u2) && (u1 || u3).
Proof.
  intros.
  rewrite <- negu_negu with (u := u1 || u2 && u3).
  rewrite de_morgan_oru with (u1 := u1) (u2 := u2 && u3).
  rewrite de_morgan_andu with (u1 := u2) (u2 := u3).
  rewrite andu_distr_oru with (u1 := -u1) (u2 := -u2) (u3 := -u3).
  rewrite <- de_morgan_oru. rewrite <- de_morgan_oru.
  rewrite de_morgan_oru. rewrite negu_negu. rewrite negu_negu.
  reflexivity.
Qed.

End NoDestruct.