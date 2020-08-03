From Undecidability Require Export PrettyBounds.

From Undecidability Require Export Code.CaseNat.
From Undecidability Require Export Code.CasePair.

From Undecidability Require Export TM.Code.CodeTM TM.Code.Copy.


(* This definition doesn't work, because we need the quantifier for all values after [(s: nat)] *)
(*
Definition dominatedWith_vec (n : nat) (f : Vector.t (nat->nat) n) (g : Vector.t (nat->nat) n) :=
  { c | forall (i : Fin.t n) (s : nat), f @>i s <=(c[@i]) g @>i s }.
*)


From Undecidability Require Import ListTM CaseList.

From Undecidability Require Export MaxList.


Fixpoint sum_list_rec (s : nat) (xs : list nat) :=
  match xs with
  | nil => s
  | x :: xs' => sum_list_rec (s + x) xs'
  end.

Lemma sum_list_rec_plus (s1 s2 : nat) (xs : list nat) :
  sum_list_rec (s1 + s2) xs = s1 + sum_list_rec s2 xs.
Proof.
  revert s1 s2. induction xs as [ | x xs IH]; intros; cbn in *.
  - reflexivity.
  - rewrite IH. rewrite IH. lia.
Qed.

Lemma sum_list_rec_S (s : nat) (xs : list nat) :
  sum_list_rec (S s) xs = S (sum_list_rec s xs).
Proof. change (S s) with (1 + s). apply sum_list_rec_plus. Qed.

Lemma sum_list_rec_ge (s : nat) (xs : list nat) :
  s <= sum_list_rec s xs.
Proof.
  induction xs as [ | x xs]; cbn in *.
  - reflexivity.
  - rewrite sum_list_rec_plus. lia.
Qed.


(*
Lemma Constr_pair_size_nice :
  { c | forall (s : nat) Constr_pair_size
*)

Global Arguments Encode_list_size {sigX X cX}.
Global Arguments size : simpl never.


(** Do something with the [k]th element in a chain of conjunctions *) 
Ltac projk_fix C H k :=
  lazymatch k with
  | 0 => C (proj1 H) + C H
  | 1 => projk_fix C (proj2 H) 0
  | S ?k' => projk_fix C (proj2 H) k'
  end.

(** Try to do something with every element in the chain of conjunctions *)
Ltac proj_fix C H :=
  lazymatch type of H with
  | ?P1 /\ ?P2 => C (proj1 H) + proj_fix C (proj2 H)
  | _ => C H
  end.

Tactic Notation "projk_rewrite"     constr(H) constr(k) := projk_fix ltac:(fun c => erewrite   c) H k.
Tactic Notation "projk_rewrite" "->" constr(H) constr(k) := projk_fix ltac:(fun c => erewrite <- c) H k.
Tactic Notation "projk_rewrite" "<-" constr(H) constr(k) := projk_fix ltac:(fun c => erewrite <- c) H k.

(** If we leave out the number, just try every proposition in the conjunction chain *)
Tactic Notation "projk_rewrite"     constr(H) := proj_fix ltac:(fun c => erewrite   c) H.
Tactic Notation "projk_rewrite" "->" constr(H) := proj_fix ltac:(fun c => erewrite -> c) H.
Tactic Notation "projk_rewrite" "<-" constr(H) := proj_fix ltac:(fun c => erewrite <- c) H.
