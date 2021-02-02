(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia Relations.

From Undecidability.MinskyMachines
  Require Import MMA mma_defs ndMM2.

From Undecidability.Shared.Libs.DLW 
  Require Import utils Vec.pos Vec.vec Code.sss.

From Undecidability.Synthetic
  Require Import Definitions ReducibilityFacts.

Set Implicit Arguments.

Set Default Proof Using "Type".

Section MMA2_ndMM2.

  Notation STOPₙ := (@ndmm2_stop _).
  Notation INCₙ  := (@ndmm2_inc _).
  Notation DECₙ  := (@ndmm2_dec _).
  Notation ZEROₙ := (@ndmm2_zero _).

  Notation α := true. 
  Notation β := false.

  Definition mma2_instr_enc i (ρ : mm_instr (pos 2)) :=
    match ρ with
      | INCₐ pos0   => INCₙ α i (1+i) :: nil
      | INCₐ _      => INCₙ β i (1+i) :: nil
      | DECₐ pos0 j => DECₙ α i j :: ZEROₙ α  i (1+i) :: nil
      | DECₐ _    j => DECₙ β i j :: ZEROₙ β i (1+i) :: nil
    end.

  Fixpoint mma2_linstr_enc i l :=
    match l with
      | nil => nil
      | ρ::l => mma2_instr_enc i ρ ++ mma2_linstr_enc (1+i) l
    end.

  Fact mma2_linstr_enc_app i l m : mma2_linstr_enc i (l++m) = mma2_linstr_enc i l ++ mma2_linstr_enc (length l+i) m.
  Proof.
    revert i; induction l as [ | ? l IHl ]; intros ?; simpl; auto.
    rewrite app_ass, IHl; do 3 f_equal; auto.
  Qed.

  Fact mma2_linstr_enc_In i P c : 
          In c (mma2_linstr_enc i P) 
       -> exists l r ρ, P = l++ρ::r /\ In c (mma2_instr_enc (length l+i) ρ).
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

  Notation "i // s -1> t" := (mma_sss i s t).
  Notation "P // r :1> s" := (sss_step (@mma_sss _) P r s)  (at level 70, no associativity).
  Notation "P // s ↠ t" := (sss_compute (@mma_sss _) P s t) (at level 70, no associativity).
  Notation "P // s ~~> t" := (sss_output (@mma_sss _) P s t).

  Local Fact mma2_instr_enc_sound Σ ρ s1 s2 : 
          ρ // s1 -1> s2 
       -> match s1, s2 with  
            | (i,v1), (j,v2) => 
            let a  := vec_pos v1 pos0 in
            let b  := vec_pos v1 pos1 in
            let a' := vec_pos v2 pos0 in
            let b' := vec_pos v2 pos1 
            in    incl (mma2_instr_enc i ρ) Σ 
               -> Σ // a' ⊕ b' ⊦ j 
               -> Σ // a  ⊕ b  ⊦ i
          end.
  Proof.
    induction 1 as [ i x v | i x k v Hv | i x k v u Hv ]; try revert Hv;
      vec split v with a; vec split v with b; vec nil v; repeat invert pos x; simpl.
    + constructor 2 with (1+i); auto.
    + constructor 3 with (1+i); auto.
    + intros -> ?; constructor 6 with (1+i); auto.
    + intros -> ?; constructor 7 with (1+i); auto.
    + intros -> ?; constructor 4 with k; auto.
    + intros -> ?; constructor 5 with k; auto.
  Qed.

  Local Fact mma2_step_linstr_sound Σ P s1 s2 : 
          (1,P) // s1 :1> s2 
       -> match s1, s2 with  
            | (i,v1), (j,v2) => 
            let a  := vec_pos v1 pos0 in
            let b  := vec_pos v1 pos1 in
            let a' := vec_pos v2 pos0 in
            let b' := vec_pos v2 pos1 
            in    incl (mma2_linstr_enc 1 P) Σ 
               -> Σ // a' ⊕ b' ⊦ j 
               -> Σ // a  ⊕ b  ⊦ i
          end.
  Proof.
    intros (n & L & ρ & R & v & H1 & H2 & H3).
    subst s1; destruct s2 as (j,w).
    inversion H1; subst n P; clear H1; simpl.
    intros H; apply (mma2_instr_enc_sound _ H3).
    apply incl_tran with (2 := H).
    rewrite mma2_linstr_enc_app; simpl.
    rewrite plus_comm.
    apply incl_appr, incl_appl, incl_refl.
  Qed.

  Variable P : list (mm_instr (pos 2)).

  Definition mma2_prog_enc := STOPₙ 0 :: mma2_linstr_enc 1 P.
  Notation Σ := mma2_prog_enc.

  Local Lemma mma2_prog_enc_compute s1 s2 : 
          (1,P) // s1 ↠ s2 
       -> match s1, s2 with  
            | (i,v1), (j,v2) => 
            let a  := vec_pos v1 pos0 in
            let b  := vec_pos v1 pos1 in
            let a' := vec_pos v2 pos0 in
            let b' := vec_pos v2 pos1 
            in    Σ // a' ⊕ b' ⊦ j 
               -> Σ // a  ⊕ b  ⊦ i
          end.
  Proof.
    intros (n & Hn).
    induction Hn as [ (i,v) | n (i,st1) (j,st2) (k,st3) H1 H2 IH2 ]; simpl; auto.
    revert IH2; simpl; intros IH3 H; generalize (IH3 H).
    apply (mma2_step_linstr_sound _ H1), incl_tl, incl_refl.
  Qed. 
 
  Local Lemma mma2_prog_enc_stop : Σ // 0 ⊕ 0 ⊦ 0.
  Proof. constructor 1; simpl; auto. Qed.

  Hint Resolve mma2_prog_enc_stop : core.

  Notation ø := vec_nil.

  Local Lemma mma2_prog_enc_complete a b p : 
             Σ // a ⊕ b ⊦ p -> (1,P) // (p,a##b##ø) ↠ (0,0##0##ø).
  Proof.
    induction 1 as [ u H 
                   | a b u v H H1 IH1
                   | a b u v H H1 IH1
                   | a b u v H H1 IH1
                   | a b u v H H1 IH1
                   | b p u H H1 IH1
                   | a p u H H1 IH1 ].
    + destruct H as [ H | H ]. 
      * inversion H; subst u. 
        exists 0; constructor 1.
      * apply mma2_linstr_enc_In in H
          as (l & r & [ x | x ] & H1 & H2); repeat invert pos x; simpl in H2.
        1-2: now destruct H2.
        1-2: now destruct H2 as [ | [] ].
    + destruct H as [ H | H ]; try discriminate.
      apply mma2_linstr_enc_In in H
        as (l & r & [ x | x ] & H3 & H2); repeat invert pos x; simpl in H2.
      2: now destruct H2.
      2-3: now destruct H2 as [ | [] ].
      destruct H2 as [ H2 | [] ]; inversion H2; subst.
      apply sss_compute_trans with (2 := IH1).
      rewrite H3.
      mma sss INC with pos0.
      mma sss stop.
    + destruct H as [ H | H ]; try discriminate.
      apply mma2_linstr_enc_In in H
        as (l & r & [ x | x ] & H3 & H2); repeat invert pos x; simpl in H2.
      1: now destruct H2.
      2-3: now destruct H2 as [ | [] ].
      destruct H2 as [ H2 | [] ]; inversion H2; subst.
      apply sss_compute_trans with (2 := IH1).
      rewrite H3.
      mma sss INC with pos1.
      mma sss stop.
    + destruct H as [ H | H ]; try discriminate.
      apply mma2_linstr_enc_In in H
        as (l & r & [ x | x ] & H3 & H2); repeat invert pos x; simpl in H2.
      1-2: now destruct H2.
      2: now destruct H2 as [ | [] ].
      destruct H2 as [ H2 | H2 ].
      2: now destruct H2.
      inversion H2; subst.
      apply sss_compute_trans with (2 := IH1).
      rewrite H3.
      mma sss DEC S with pos0 v a.
      mma sss stop.
    + destruct H as [ H | H ]; try discriminate.
      apply mma2_linstr_enc_In in H
        as (l & r & [ x | x ] & H3 & H2); repeat invert pos x; simpl in H2.
      1-2: now destruct H2.
      1: now destruct H2 as [ | [] ].
      destruct H2 as [ H2 | H2 ].
      2: now destruct H2.
      inversion H2; subst.
      apply sss_compute_trans with (2 := IH1).
      rewrite H3.
      mma sss DEC S with pos1 v b.
      mma sss stop.
    + destruct H as [ H | H ]; try discriminate.
      apply mma2_linstr_enc_In in H
        as (l & r & [ x | x j ] & H3 & H2); repeat invert pos x; simpl in H2.
      1-2: now destruct H2.
      2: now destruct H2 as [ | [] ].
      destruct H2 as [ H2 | [ H2 | [] ] ].
      1: easy.
      inversion H2; subst.
      apply sss_compute_trans with (2 := IH1).
      rewrite H3.
      mma sss DEC 0 with pos0 j.
      mma sss stop.
    + destruct H as [ H | H ]; try discriminate.
      apply mma2_linstr_enc_In in H
        as (l & r & [ x | x j ] & H3 & H2); repeat invert pos x; simpl in H2.
      1-2: now destruct H2.
      1: now destruct H2 as [ | [] ].
      destruct H2 as [ H2 | [ H2 | [] ] ].
      1: easy.
      inversion H2; subst.
      apply sss_compute_trans with (2 := IH1).
      rewrite H3.
      mma sss DEC 0 with pos1 j.
      mma sss stop.
  Qed.

  Theorem MMA2_ndMM2_equiv a b : MMA2_HALTS_ON_ZERO (P,a##b##ø) <-> Σ // a ⊕ b ⊦ 1.
  Proof.
    split.
    + intros (H1 & _). 
      apply mma2_prog_enc_compute in H1.
      apply H1; auto.
    + intros H1; split.
      * apply mma2_prog_enc_complete, H1.
      * simpl; lia.
  Qed.

End MMA2_ndMM2.

Theorem reduction : MMA2_HALTS_ON_ZERO ⪯ @ndMM2_ACCEPT nat.
Proof.
  apply reduces_dependent; exists.
  intros (P & v). 
  vec split v with a; vec split v with b; vec nil v.
  exists (existT _ (mma2_prog_enc P) (1,(a,b))).
  apply MMA2_ndMM2_equiv.
Qed.
