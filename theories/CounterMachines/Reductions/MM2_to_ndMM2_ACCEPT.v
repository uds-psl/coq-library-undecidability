(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia Relations.

Require Import Undecidability.MinskyMachines.MM2.
Require Import Undecidability.CounterMachines.ndMM2.

From Undecidability.Shared.Libs.DLW 
  Require Import utils.

From Undecidability.Synthetic
  Require Import Definitions ReducibilityFacts.

Set Implicit Arguments.

Section MM2_ndMM2.

  Notation STOP := (@ndmm2_stop _).
  Notation INC  := (@ndmm2_inc _).
  Notation DEC  := (@ndmm2_dec _).
  Notation ZERO := (@ndmm2_zero _).

  Notation α := true. 
  Notation β := false.

  Definition mm2_instr_enc i ρ :=
    match ρ with
      | mm2_inc_a   => INC α i (1+i) :: nil
      | mm2_inc_b   => INC β i (1+i) :: nil
      | mm2_dec_a j => DEC α i j :: ZERO true  i (1+i) :: nil
      | mm2_dec_b j => DEC β i j :: ZERO false i (1+i) :: nil
    end.

  Fixpoint mm2_linstr_enc i l :=
    match l with
      | nil => nil
      | ρ::l => mm2_instr_enc i ρ ++ mm2_linstr_enc (1+i) l
    end.

  Fact mm2_linstr_enc_app i l m : mm2_linstr_enc i (l++m) = mm2_linstr_enc i l ++ mm2_linstr_enc (length l+i) m.
  Proof.
    revert i; induction l as [ | ? l IHl ]; intros ?; simpl; auto.
    rewrite app_ass, IHl; do 3 f_equal; auto.
  Qed.

  Fact mm2_linstr_enc_In i P c : 
          In c (mm2_linstr_enc i P) 
       -> exists l r ρ, P = l++ρ::r /\ In c (mm2_instr_enc (length l+i) ρ).
  Proof.
    revert i; induction P as [ | ρ P IH ]; intros i.
    + intros [].
    + simpl; rewrite in_app_iff; intros [ H | H ].
      * exists nil, P, ρ; split; auto.
      * destruct (IH (1+i)) as (l & r & ρ' & H1 & H2); auto.
        exists (ρ::l), r, ρ'; split; auto.
        - simpl; f_equal; auto.
        - eq goal H2; do 2 f_equal; simpl; lia.
  Qed.

  Notation "Σ // a ⊕ b ⊦ u" := (ndmm2_accept Σ a b u) (at level 70, no associativity).

  Local Fact mm2_instr_enc_sound Σ ρ s1 s2 : 
          mm2_atom ρ s1 s2 
       -> match s1, s2 with 
            | (i,(a,b)), (j,(a',b')) => incl (mm2_instr_enc i ρ) Σ 
                                     -> Σ // a' ⊕ b' ⊦ j 
                                     -> Σ // a  ⊕ b  ⊦ i
          end.
  Proof.
    induction 1 as [ i a b | i a b | i j a b | i j a b | i j b | i j a ]; simpl; intros HΣ H.
    + constructor 2 with (1+i); auto; apply HΣ; simpl; auto.
    + constructor 3 with (1+i); auto; apply HΣ; simpl; auto.
    + constructor 4 with j; auto; apply HΣ; simpl; auto.
    + constructor 5 with j; auto; apply HΣ; simpl; auto.
    + constructor 6 with (1+i); auto; apply HΣ; simpl; auto.
    + constructor 7 with (1+i); auto; apply HΣ; simpl; auto.
  Qed.

  Local Fact mm2_step_linstr_sound Σ P s1 s2 : 
          mm2_step P s1 s2 
       -> match s1, s2 with 
            | (i,(a,b)), (j,(a',b')) => incl (mm2_linstr_enc 1 P) Σ 
                                     -> Σ // a' ⊕ b' ⊦ j 
                                     -> Σ // a  ⊕ b  ⊦ i
          end.
  Proof.
    intros (ρ & (l&r&H1&H2) & H3).
    apply mm2_instr_enc_sound with (Σ := Σ) in H3; revert s1 s2 H2 H3.
    intros (i,(a,b)) (j,(a',b')); simpl; intros H2 H3 H4 H5.
    apply H3; auto.
    apply incl_tran with (2 := H4).
    rewrite H1, mm2_linstr_enc_app.
    apply incl_appr; simpl.
    apply incl_appl.
    rewrite <- H2, plus_comm.
    apply incl_refl.
  Qed.

  Notation "P // x ↠ y" := (clos_refl_trans _ (mm2_step P) x y) (at level 70).

  Variable P : list mm2_instr.

  Definition mm2_prog_enc := STOP 0 :: mm2_linstr_enc 1 P.

  Notation Σ := mm2_prog_enc.

  Local Lemma mm2_prog_enc_compute s1 s2 : 
          P // s1 ↠ s2 
       -> match s1, s2 with 
            | (i,(a,b)), (j,(a',b')) => Σ // a' ⊕ b' ⊦ j 
                                     -> Σ // a  ⊕ b  ⊦ i
          end.
  Proof.
    induction 1 as [ (?,(?,?)) (?,(?,?)) H
                   | (?,(?,?)) 
                   | (?,(?,?)) (?,(?,?)) (?,(?,?))  ]; eauto.
    apply mm2_step_linstr_sound with (Σ := Σ) in H.
    apply H, incl_tl, incl_refl.
  Qed.

  Local Lemma mm2_prog_enc_stop : Σ // 0 ⊕ 0 ⊦ 0.
  Proof. constructor 1; simpl; auto. Qed.

  Hint Resolve mm2_prog_enc_stop : core.

  Local Lemma mm2_prog_enc_complete a b p : 
             Σ // a ⊕ b ⊦ p -> P // (p,(a,b)) ↠ (0,(0,0)).
  Proof.
    induction 1 as [ u H 
                   | a b u v H H1 IH1
                   | a b u v H H1 IH1
                   | a b u v H H1 IH1
                   | a b u v H H1 IH1
                   | b p u H H1 IH1
                   | a p u H H1 IH1 ].
    + destruct H as [ H | H ]. 
      * inversion H; subst u; constructor 2.
      * apply mm2_linstr_enc_In in H
          as (l & r & [ | | | ] & H1 & H2); simpl in H2.
        1-2: now destruct H2.
        1-2: now destruct H2 as [ | [] ].
    + destruct H as [ H | H ]; try discriminate.
      apply mm2_linstr_enc_In in H
        as (l & r & [ | | | ] & H3 & H2); simpl in H2.
      2: now destruct H2.
      2-3: now destruct H2 as [ | [] ].
      destruct H2 as [ H2 | [] ]; inversion H2; subst.
      constructor 3 with (length l+2, (S a,b)).
      * constructor 1.
        exists mm2_inc_a; split.
        - exists l, r; simpl; split; auto; lia.
        - rewrite !(plus_comm (length l)); constructor.
      * eq goal IH1; do 2 f_equal; lia.
    + destruct H as [ H | H ]; try discriminate.
      apply mm2_linstr_enc_In in H
        as (l & r & [ | | | ] & H3 & H2); simpl in H2.
      1: now destruct H2.
      2-3: now destruct H2 as [ | [] ].
      destruct H2 as [ H2 | [] ]; inversion H2; subst.
      constructor 3 with (length l+2, (a,S b)).
      * constructor 1.
        exists mm2_inc_b; split.
        - exists l, r; simpl; split; auto; lia.
        - rewrite !(plus_comm (length l)); constructor.
      * eq goal IH1; do 2 f_equal; lia.
    + destruct H as [ H | H ]; try discriminate.
      apply mm2_linstr_enc_In in H
        as (l & r & [ | | | ] & H3 & H2); simpl in H2.
      1-2: now destruct H2.
      2: now destruct H2 as [ | [] ].
      destruct H2 as [ H2 | H2 ].
      2: now destruct H2.
      inversion H2; subst.
      constructor 3 with (v, (a,b)); auto.
      constructor 1.
      exists (mm2_dec_a v); split; auto.
      * exists l, r; simpl; split; auto; lia.
      * rewrite !(plus_comm (length l)); constructor.
    + destruct H as [ H | H ]; try discriminate.
      apply mm2_linstr_enc_In in H
        as (l & r & [ | | | ] & H3 & H2); simpl in H2.
      1-2: now destruct H2.
      1: now destruct H2 as [ | [] ].
      destruct H2 as [ H2 | H2 ].
      2: now destruct H2.
      inversion H2; subst.
      constructor 3 with (v, (a,b)); auto.
      constructor 1.
      exists (mm2_dec_b v); split; auto.
      * exists l, r; simpl; split; auto; lia.
      * rewrite !(plus_comm (length l)); constructor.
    + destruct H as [ H | H ]; try discriminate.
      apply mm2_linstr_enc_In in H
        as (l & r & [ | | | ] & H3 & H2); simpl in H2.
      1-2: now destruct H2.
      2: now destruct H2 as [ | [] ].
      destruct H2 as [ H2 | [ H2 | [] ] ].
      1: easy.
      inversion H2; subst.
      constructor 3 with (length l+2, (0,b)).
      * constructor 1.
        exists (mm2_dec_a n); split.
        - exists l, r; simpl; split; auto; lia.
        - rewrite !(plus_comm (length l)); constructor.
      * eq goal IH1; do 2 f_equal; lia.
    + destruct H as [ H | H ]; try discriminate.
      apply mm2_linstr_enc_In in H
        as (l & r & [ | | | ] & H3 & H2); simpl in H2.
      1-2: now destruct H2.
      1: now destruct H2 as [ | [] ].
      destruct H2 as [ H2 | [ H2 | [] ] ].
      1: easy.
      inversion H2; subst.
      constructor 3 with (length l+2, (a,0)).
      * constructor 1.
        exists (mm2_dec_b n); split.
        - exists l, r; simpl; split; auto; lia.
        - rewrite !(plus_comm (length l)); constructor.
      * eq goal IH1; do 2 f_equal; lia.
  Qed.

  Theorem MM2_ndMM2_equiv a b : MM2_HALTS_ON_ZERO (P,a,b) <-> Σ // a ⊕ b ⊦ 1.
  Proof.
    split.
    + intros H; apply mm2_prog_enc_compute in H; auto.
    + apply mm2_prog_enc_complete.
  Qed.

End MM2_ndMM2.

Theorem reduction : MM2_HALTS_ON_ZERO ⪯ @ndMM2_ACCEPT nat.
Proof.
  apply reduces_dependent; exists.
  intros ((P,a),b).
  exists (existT _ (mm2_prog_enc P) (1,(a,b))).
  apply MM2_ndMM2_equiv.
Qed.
