From Undecidability.L Require Import Tactics.LTactics Datatypes.LUnit Datatypes.LBool Datatypes.LNat.
Require Import BinNums.
Require Import Undecidability.L.Tactics.GenEncode.

(** ** Encoding of positive binary numbers *)
Run TemplateProgram (tmGenEncode "positive_enc" positive).
Hint Resolve positive_enc_correct : Lrewrite.

Global Instance termT_Pos_xI : computableTime' xI (fun x _ => (1,tt)).
extract constructor. solverec.
Qed.

Global Instance termT_Pos_xO : computableTime' xO (fun x _ => (1,tt)).
extract constructor. solverec.
Qed.

Global Instance termT_Pos_succ : computableTime' Pos.succ (fun x _ => (Pos.size_nat x*11,tt)).
extract. solverec.
Qed.

(** ** Encoding of natural binary numbers *)
Run TemplateProgram (tmGenEncode "N_enc" N).
Hint Resolve N_enc_correct : Lrewrite.

Instance termT_N_NPos : computableTime' Npos (fun x _ => (1,tt)).
  extract constructor. solverec.
Qed.

(** *** basic functions *)

Lemma pos_size_eq_log2 n : Pos.size_nat n = Nat.log2 (Pos.to_nat n) + 1.
Proof.
  induction n;cbn.
  3:reflexivity.
  all:rewrite IHn.
  2:{rewrite Pos2Nat.inj_xO. rewrite Nat.log2_double. 2:now apply Pos2Nat.is_pos. now Lia.lia. }
  {rewrite Pos2Nat.inj_xI.
   transitivity (S (S (Nat.log2 (Pos.to_nat n)))). Lia.lia.
   rewrite <- Nat.log2_succ_double. 2:now apply Pos2Nat.is_pos. rewrite Nat.add_1_r. Lia.nia. }
Qed. 

Lemma pos_size_nat_eq n: Pos.size_nat n = Pos.to_nat (Pos.size n).
Proof.
  induction n;cbn.
  3:reflexivity.
  all:rewrite IHn.
  all:now rewrite Pos2Nat.inj_succ.
Qed.

Lemma pos_size_nat_leq n : Pos.size_nat n <= Pos.to_nat n.
Proof. 
  rewrite pos_size_nat_eq. apply Pos2Nat.inj_le.
  induction n;cbn. 3:reflexivity. all:Lia.lia.
Qed.

Lemma Pos_size_nat_leq p : (Pos.size p <= p)%positive.
Proof.
  induction p. all:cbn. all:try Lia.lia.
Qed.

Lemma N_size_nat_leq' n : (N.size n <= n)%N.
Proof.
  destruct n. now reflexivity.
  cbn. apply Pos_size_nat_leq.
Qed.

Lemma N_size_nat_eq n : N.size_nat n = N.to_nat (N.size n).
Proof.
  destruct n. reflexivity.
  cbn. apply pos_size_nat_eq.
Qed.

Lemma N_size_nat_leq n : (N.size_nat (N.of_nat n)) <= n.
Proof.
  rewrite N_size_nat_eq.
  etransitivity. 2:rewrite <- Nnat.Nat2N.id;reflexivity.
  eapply Nat.compare_le_iff. rewrite <- Nnat.N2Nat.inj_compare. apply N_size_nat_leq'.
Qed.


(* One probably could do better by repeated halving (O(n)) *)
Definition time_N_of_nat n := n* 20 + n*Nat.log2 n*11.

Local Arguments Nat.log2 : simpl never.

Instance term_Pos_of_succ_nat : computableTime' Pos.of_succ_nat (fun n _ => (time_N_of_nat n +8,tt)).
  extract. solverec. fold Pos.of_succ_nat. unfold time_N_of_nat.
  rewrite pos_size_eq_log2,SuccNat2Pos.id_succ.
  change (1 + n) with (S n).
  rewrite (Nat.log2_le_mono n (S n)). all:Lia.nia.
Qed.

Instance term_N_of_nat : computableTime' N.of_nat (fun n _ => (time_N_of_nat n+ 4,tt)).
Proof.
  extract. solverec. unfold time_N_of_nat.
  rewrite (Nat.log2_le_mono n (S n)).
  all:ring_simplify. all:Lia.nia.
Qed.

Arguments time_N_of_nat : simpl never.

Instance term_N_succ : computableTime' N.succ (fun x _ => (N.size_nat x * 11 + 6,tt)).
Proof.
  extract. solverec.
Qed.

Lemma N_size_nat_monotone n n' : (n <= n')%N -> N.size_nat n <= N.size_nat n'.
Proof.
  intros ?. destruct (N.eqb_spec n n'). now subst.
  destruct n, n'. all:cbn in *. all:try Lia.lia. apply Pos.size_nat_monotone. Lia.lia. 
Qed.
Lemma N_size_nat_add_leq x y : N.size_nat (x+y) <= 1 + max (N.size_nat x) (N.size_nat y).
Proof.
  destruct x,y;cbn. 1-3:Lia.nia.
  rewrite !pos_size_eq_log2.
  destruct (@Pos.leb_spec0 p p0).
  2:rename n into l;apply Pos.lt_nle,Pos.lt_le_incl in l. 
  all:setoid_rewrite l at 1.
  replace (p0 + p0)%positive with (2*p0)%positive;[|Lia.lia].
  2:  replace (p + p)%positive with (2*p)%positive;[|Lia.lia].
  all:rewrite Pos2Nat.inj_mul.
  all:change (Pos.to_nat 2) with 2.
  all:rewrite Nat.log2_double;[|now eauto using Pos2Nat.is_pos]. all:Lia.lia.
Qed.
