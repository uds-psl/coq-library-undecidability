From Undecidability.L.Tactics Require Import LTactics.
Require Import PslBase.Base.
From Undecidability.L.Computability Require Import Enum.
From Undecidability.L.Functions Require Import Encoding Equality.
From Undecidability.L.Datatypes Require Import LNat Lists LProd.

(** ** Enumeratibility of L-terms *)
Instance term_appCross : computableTime' appCross (fun A _ => (5,fun B _ => (length A * length B * 29 + length A * 30 +  4,tt))).
Proof.
  extract. solverec. fold appCross;rewrite map_time_const,map_length. Lia.nia.
Defined.

Instance term_exh_size : computable exh_size.
Proof.
  extract.
Defined.

Definition T_nondec_helper A x : bool
  :=  negb (inb term_eqb x A)  .

Fixpoint T_nondec (n : nat) : list term :=
  match n with
  | 0 => [# n]
  | S n0 =>
    T_nondec n0 ++
             [# (S n0)] ++
             filter (T_nondec_helper (T_nondec n0)) (map lam (T_nondec n0) ++ appCross (T_nondec n0) (T_nondec n0))
  end.

Lemma T_nondec_correct : forall n, T n = T_nondec n.
Proof.
  induction n. reflexivity.
  simpl. unfold T_nondec_helper. do 2 f_equal. rewrite <-IHn.
  generalize ((map lam (T n) ++ appCross (T n) (T n)): list term). generalize (T n).
  induction l0. simpl.  reflexivity.
  simpl.
  rewrite IHl0.
  edestruct (inb_spec term_eqb_spec a l);dec;try (exfalso;tauto);reflexivity.
Qed.

Local Instance term_T_nondec : computable T_nondec.
Proof.
  assert (computable T_nondec_helper).
  extract.
  extract.
Defined.


Instance term_T : computable T.
Proof.
  eapply computableExt with (x:= T_nondec).  2:exact _.
  repeat intro. symmetry. apply T_nondec_correct.
Defined.

Instance term_g_inv : computable g_inv.
Proof. unfold g_inv.
       extract.
Defined.

Definition g_nondec s :=
  match pos_nondec term_eqb s (T (exh_size s)) with
  | Some n => n
  | None => 0
  end.

Lemma g_nondec_correct : forall n, g n = g_nondec n.
Proof.
  unfold g, g_nondec.
  setoid_rewrite pos_nondec_spec. reflexivity. apply term_eqb_spec.
Qed.

Local Instance term_g_nondec : computable g_nondec.
Proof.
  unfold g_nondec.
  extract.
Defined.


Instance term_g : computable g.
Proof.
  eapply computableExt with (x:= g_nondec).  2:exact _.
  repeat intro. symmetry. apply g_nondec_correct.
Defined.

Local Definition f_filter A x := negb (inb (prod_eqb Nat.eqb Nat.eqb) x A).
Local Definition f_map (p : nat * nat) := let (p1, p2) := p in (p1, S p2).

Fixpoint C_nondec (n : nat) : list (nat * nat) :=
  match n with
  | 0 => [(0, 0)]
  | S n0 => let C' := C_nondec n0 in
           C' ++
              (S n0, 0)
              :: filter (f_filter C')
              (map f_map C')
  end.

Lemma C_nondec_correct : forall n, C n = C_nondec n.
Proof.
  induction n. reflexivity.
  simpl. do 2 f_equal. rewrite <-IHn. fold f_map.
  generalize ((map f_map (C n))). generalize (C n).
  induction l0;cbn. reflexivity.
  rewrite IHl0. unfold f_filter at 3.
  edestruct (inb_spec (prod_eqb_spec Nat.eqb_spec Nat.eqb_spec) a l); decide (~ a el l); try (exfalso;tauto);reflexivity.
Qed.


Local Instance term_C_nondec : computable C_nondec.
Proof.
  assert (computable f_filter) by extract.
  assert (computable f_map) by extract.
  extract.
Defined.


Instance term_C : computable C.
Proof.
  eapply computableExt with (x:= C_nondec).  2:exact _.
  repeat intro. symmetry. apply C_nondec_correct.
Defined.

Instance term_eSize : computable eSize.
Proof.
  extract.
Qed.

Instance term_c : computable c.
Proof.
  unfold c. (* TODO: Wy is this needed?*)
  extract. 
Qed.
