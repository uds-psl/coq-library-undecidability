(* * Pointer bookkeeping for machines using (positive) binary numbers *)

From Undecidability.TM Require Import ProgrammingTools.
From Undecidability Require Import BinNumbers.EncodeBinNumbers.
From Undecidability Require Import BinNumbers.PosDefinitions.

Local Open Scope positive_scope.


Definition atBit (t : tape sigPos^+) (lp : positive) (mb : bool) (rs : list bool) :=
  exists (ls : list sigPos^+),
    t = midtape (map inr (rev (encode lp)) ++ inl START :: ls) (bitToSigPos' mb) (map bitToSigPos' rs ++ [inl STOP]).

Definition atLSB (t : tape sigPos^+) (lp : positive) (mb : bool) := atBit t lp mb nil.

Lemma atLSB_moveRight_contains_rev (t : tape sigPos^+) (lp : positive) (mb : bool) :
  atLSB t lp mb ->
  tape_move t Rmove ≂ lp ~~ mb.
Proof.
  intros (ls&->); cbn. hnf; destruct mb; cbn; eexists; f_equal.
  - unfold bitToSigPos'; cbn. simpl_list. rewrite <- map_rev; cbn. simpl_list. f_equal. f_equal.
    rewrite !map_rev. f_equal. now rewrite map_id.
  - unfold bitToSigPos'; cbn. simpl_list. rewrite <- map_rev; cbn. simpl_list. f_equal. f_equal.
    rewrite !map_rev. f_equal. now rewrite map_id.
Qed.


Lemma atBit_moveRight_cons (t : tape sigPos^+) (lp : positive) (b b' : bool) (rs : list bool) :
  atBit t lp b (b' :: rs) ->
  atBit (tape_move t Rmove) (lp ~~ b) b' rs.
Proof.
  intros (ls&->). hnf. cbn.
  rewrite Encode_positive_app_xIO. rewrite rev_app_distr. cbn.
  destruct b; cbn.
  - eexists. f_equal.
  - eexists. f_equal.
Qed.


Lemma atBit_moveRight (t : tape sigPos^+) (lp : positive) (b : bool) (rs : list bool) :
  atBit t lp b rs ->
  match rs with
  | nil => tape_move t Rmove ≂ lp ~~ b
  | b' :: rs' => atBit (tape_move t Rmove) (lp ~~ b) b' rs'
  end.
Proof.
  intros H. destruct rs as [ | b' rs'].
  - now apply atLSB_moveRight_contains_rev.
  - now apply atBit_moveRight_cons.
Qed.


Lemma contains_rev_moveLeft_atLSB (t : tape sigPos^+) (lp : positive) (mb : bool) :
  t ≂ (lp ~~ mb) ->
  atLSB (tape_move t Lmove) lp mb.
Proof.
  intros (ls&->); cbn. hnf.
  rewrite Encode_positive_app_xIO.
  rewrite <- !map_rev.
  destruct mb; cbn.
  - rewrite rev_app_distr; cbn. eexists. f_equal. f_equal. f_equal. now rewrite map_id.
  - rewrite rev_app_distr; cbn. eexists. f_equal. f_equal. f_equal. now rewrite map_id.
Qed.

Lemma atBit_moveLeft_cons (t : tape sigPos^+) (lp : positive) (b b' : bool) (rs : list bool) :
  atBit t (lp ~~ b) b' rs ->
  atBit (tape_move t Lmove) lp b (b' :: rs).
Proof.
  intros (ls&->); cbn. hnf.
  rewrite Encode_positive_app_xIO.
  destruct b; cbn.
  - exists ls. simpl_list. cbn. f_equal.
  - exists ls. simpl_list. cbn. f_equal.
Qed.

Definition atHSB (t : tape sigPos^+) (p : positive) :=
  exists (ls : list sigPos^+),
    t = midtape (inl START :: ls) (inr sigPos_xH) (map inr (tl (encode p)) ++ [inl STOP]).

Lemma atHSB_moveLeft_contains (t : tape sigPos^+) (p : positive) :
  atHSB t p ->
  tape_move t Lmove ≃ p.
Proof.
  intros (ls&->). hnf. cbn.
  pose proof Encode_positive_startsWith_xH p as (str'&H); setoid_rewrite H; clear H; cbn.
  eexists. f_equal. f_equal. now rewrite map_id.
Qed.

Lemma contains_moveRight_atHSB (t : tape sigPos^+) (p : positive) :
  t ≃ p ->
  atHSB (tape_move t Rmove) p.
Proof.
  intros (ls&->). hnf. cbn.
  pose proof Encode_positive_startsWith_xH p as (str'&H); setoid_rewrite H; clear H; cbn.
  eexists. f_equal. f_equal. now rewrite map_id.
Qed.

Lemma atBit_moveLeft_atHSB (t : tape sigPos^+) (b : bool) (rs : list bool) :
  atBit t 1 b rs ->
  atHSB (tape_move t Lmove) (bits_to_pos (b :: rs)).
Proof.
  intros (ls&->). cbn -[bits_to_pos]. hnf. exists ls. f_equal. cbn -[bits_to_pos]. rewrite app_comm_cons. f_equal.
  rewrite encode_bits_to_pos. cbn. f_equal. now rewrite map_map.
Qed.


(* *** Extensionality lemma and tactics *)

Lemma atBit_ext (t : tape sigPos^+) (p0 : positive) (b0 : bool) (bits0 : list bool) (p1 : positive) (b1 : bool) (bits1 : list bool) :
  atBit t p0 b0 bits0 ->
  p0 = p1 ->
  b0 = b1 ->
  bits0 = bits1 ->
  atBit t p1 b1 bits1.
Proof. now intros H -> -> ->. Qed.

Lemma atLSB_ext (t : tape sigPos^+) (p0 : positive) (b0 : bool) (p1 : positive) (b1 : bool) :
  atLSB t p0 b0 ->
  p0 = p1 ->
  b0 = b1 ->
  atLSB t p1 b1 .
Proof. now intros H -> ->. Qed.

Lemma atHSB_ext (t : tape sigPos^+) (p0 : positive) (p1 : positive) :
  atHSB t p0 ->
  p0 = p1 ->
  atHSB t p1.
Proof. now intros H ->. Qed.

Ltac atBit_ext :=
  once lazymatch goal with
  | [ H : atBit ?t ?p0 ?b0 ?bits0 |- atBit ?t ?p1 ?b1 ?bits0 ] => apply (atBit_ext H); auto
  | [ H : atLSB ?t ?p0 ?b0        |- atLSB ?t ?p1 ?b1        ] => apply (atLSB_ext H); auto
  | [ H : atHSB ?t ?p0            |- atHSB ?t ?p1            ] => apply (atHSB_ext H); auto
  end.

