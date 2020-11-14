From Undecidability.Shared.Libs.PSL Require Import Vectors.
Import Vector.VectorNotations Lia PeanoNat.
Require Import Equations.Prop.DepElim.

Lemma vector_fold_right_to_list (A B : Type) (f : A -> B -> B) (n : nat) (v : Vector.t A n) (a : B):
      Vector.fold_right f v a = List.fold_right f a (Vector.to_list v).
Proof. unfold Vector.to_list.
      induction n. all:destruct_vector. all:cbn;congruence.
Qed.
Lemma vector_fold_left_to_list (A B : Type) (f : A -> B -> A) (n : nat) (v : VectorDef.t B n) (a : A):
  VectorDef.fold_left f a v = List.fold_left f (Vector.to_list v) a.
Proof. unfold Vector.to_list.
      induction n in v,a|-*. all:destruct_vector. all:cbn;congruence.
Qed.

Lemma vector_rev_append_tail_to_list A (n m: nat) (v : Vector.t A n) (w : Vector.t A m): 
Vector.to_list (Vector.rev_append_tail v w) = (List.rev (Vector.to_list v) ++ Vector.to_list w)%list.
Proof.
unfold Vector.to_list. revert m w. depind v;cbn. reflexivity.
intros. specialize IHv with (w:=h::w). rewrite IHv.
autorewrite with list. easy.
Qed.

Lemma vector_rev_to_list A (n : nat) (v : Vector.t A n): 
  Vector.to_list (Vector.rev v) = List.rev (Vector.to_list v).
Proof.
  unfold Vector.rev,Vector.rev_append.
  specialize (vector_rev_append_tail_to_list v []) as H'. cbn in H'.
  autorewrite with list in H'. rewrite <- H'. generalize (Vector.rev_append_tail v []). 
  generalize (Plus.plus_tail_plus n 0). generalize (Plus.tail_plus n 0). generalize (plus_n_O n).
  intros -> ? <-. rewrite <- plus_n_O. reflexivity.
Qed.

Lemma vector_fold_left_right (A B : Type) (f : A -> B -> A) (n : nat) (v : VectorDef.t B n) (a : A):
Vector.fold_left f a v = Vector.fold_right (fun x y => f y x) (Vector.rev v) a.
Proof.
  rewrite vector_fold_right_to_list, vector_fold_left_to_list.
  setoid_rewrite <- List.rev_involutive at 2. rewrite List.fold_left_rev_right. f_equal.
  rewrite vector_rev_to_list,List.rev_involutive. easy.
Qed.

Lemma vector_map_to_list A B (f : A -> B)(n : nat) (v : Vector.t A n): 
  Vector.to_list (Vector.map f v) = List.map f (Vector.to_list v).
Proof.
  unfold Vector.map, Vector.to_list. depind v;cbn. easy. now rewrite IHv.
Qed.


Local Arguments Fin.of_nat_lt _ {_} _.

Lemma vector_nth_rev_append_tail_r' X n n' (v : Vector.t X n) (v' : Vector.t X n') i (i':=proj1_sig (Fin.to_nat i))
j (H: i' = n + j) H':
(Vector.rev_append_tail v v') [@ i] = v'[@ Fin.of_nat_lt j H'].
Proof.
  revert dependent n'. revert j.
  depind v;cbn;intros.
  {f_equal. subst j. erewrite Fin.of_nat_ext, Fin.of_nat_to_nat_inv. easy. }
  erewrite IHv with (v':=h::v') (j:=S j). 2:nia. cbn.
  f_equal. eapply Fin.of_nat_ext.
  Unshelve. nia.
Qed.

Lemma vector_nth_rev_append_tail_r X n n' (v : Vector.t X n) (v' : Vector.t X n') i (i':=proj1_sig (Fin.to_nat i))
(H : n <= i') H':
(Vector.rev_append_tail v v') [@ i] = v'[@ Fin.of_nat_lt (i' - n) H'].
Proof.
  revert dependent n'. 
  depind v;cbn;intros.
  {f_equal. revert H'. rewrite Nat.sub_0_r. intro. erewrite Fin.of_nat_ext, Fin.of_nat_to_nat_inv. easy. }
  unshelve erewrite IHv with (v':=h::v'). 3:nia. 1:abstract (clear - H'; nia).
  generalize (vector_nth_rev_append_tail_r_subproof n n' i H').
  destruct (proj1_sig (Fin.to_nat i) - n) eqn:H''. nia.
  cbn. intros. f_equal. revert H'. replace (proj1_sig (Fin.to_nat i) - S n) with n0 by nia. 
  intros. apply Fin.of_nat_ext.
Qed.

Lemma vector_nth_rev_append_tail_l X n n' (v : Vector.t X n) (v' : Vector.t X n') i (i':=proj1_sig (Fin.to_nat i))
(H: i' < n) H':
(Vector.rev_append_tail v v') [@ i] = v[@ Fin.of_nat_lt (n-1-i') H'].
Proof.
  revert dependent n'.
  depind v;cbn;intros. nia.
  revert H'. destruct (n - 0 - proj1_sig (Fin.to_nat i)) eqn:H';cbn.
  - unshelve erewrite vector_nth_rev_append_tail_r. 3:nia. 1:abstract nia.
    generalize (vector_nth_rev_append_tail_l_subproof n n' i H H').
    destruct (proj1_sig (Fin.to_nat i) - n) eqn:H''. 2:nia.
    reflexivity.
  - unshelve erewrite IHv. 3:nia. 1:abstract nia. intros. f_equal.
    generalize (vector_nth_rev_append_tail_l_subproof0 n n' i H n0 H').
    replace (n - 1 - proj1_sig (Fin.to_nat i)) with n0. 2:nia.
    intros. eapply Fin.of_nat_ext.
Qed.

Lemma vector_nth_rev X n (v : Vector.t X n) i H':
(Vector.rev v) [@ i] = v[@ Fin.of_nat_lt (n -1-proj1_sig (Fin.to_nat i)) H'].
Proof.
  unfold Vector.rev, Vector.rev_append. 
  specialize (vector_nth_rev_append_tail_l v []). cbn zeta. 
  generalize (Vector.rev_append_tail v []). generalize (Plus.plus_tail_plus n 0).
  generalize (Plus.tail_plus n 0). generalize (plus_n_O n). generalize (n+0).
  intros ? -> ? <- ? H. apply H. now destruct Fin.to_nat.
Qed.