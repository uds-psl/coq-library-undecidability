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
  Require Import utils Vec.pos Vec.vec Code.subcode Code.sss.

From Undecidability.Synthetic
  Require Import Definitions ReducibilityFacts.

Set Implicit Arguments.

Set Default Proof Using "Type".

Local Tactic Notation "vec2" hyp(v) "into" ident(x) ident(y) :=
    vec split v with x; vec split v with y; vec nil v; clear v.

Section MMA2_ndMM2.

  Notation STOPₙ := (@ndmm2_stop _).
  Notation INCₙ  := (@ndmm2_inc _).
  Notation DECₙ  := (@ndmm2_dec _).
  Notation ZEROₙ := (@ndmm2_zero _).

  Notation α := true. 
  Notation β := false.

  Infix "∊" := In (at level 70).
  Infix "⊆" := incl (at level 70).

  Notation ø := vec_nil.

  Definition pos2_to_bool (p : pos 2) :=
    match p with pos0 => α | _ => β end.

  Notation "⌈ p ⌉" := (pos2_to_bool p) (at level 1, format "⌈ p ⌉").

  Definition mma2_instr_enc i (ρ : mm_instr (pos 2)) :=
    match ρ with
      | INCₐ x   => INCₙ ⌈x⌉ i (1+i) :: nil
      | DECₐ x j => DECₙ ⌈x⌉ i j :: ZEROₙ ⌈x⌉ i (1+i) :: nil
    end.

  Notation "'⟨' i , ρ '⟩₁'" := (mma2_instr_enc i  ρ) (format "⟨ i , ρ ⟩₁").

  Reserved Notation "'⟪' i , l '⟫ₗ'" (at level 1, format "⟪ i , l ⟫ₗ").

  Fixpoint mma2_linstr_enc i l :=
    match l with
      | nil  => nil
      | ρ::l => ⟨i,ρ⟩₁ ++ ⟪1+i,l⟫ₗ
    end
  where "⟪ i , l ⟫ₗ" := (mma2_linstr_enc i l).

  Fact mma2_linstr_enc_app i l m : ⟪i,l++m⟫ₗ = ⟪i,l⟫ₗ ++ ⟪length l+i,m⟫ₗ.
  Proof.
    revert i; induction l as [ | ? l IHl ]; intros ?; simpl; auto.
    rewrite app_ass, IHl; do 3 f_equal; auto.
  Qed.

  Fact mma2_linstr_enc_In i P c : 
          c ∊ ⟪i,P⟫ₗ -> exists L ρ R, P = L++ρ::R /\ c ∊ ⟨length L+i,ρ⟩₁.
  Proof.
    revert i; induction P as [ | ρ P IH ]; intros i.
    + intros [].
    + simpl; rewrite in_app_iff; intros [ H | H ].
      * exists nil, ρ, P; split; auto.
      * destruct (IH (1+i)) as (l & ρ' & r & H1 & H2); auto.
        exists (ρ::l), ρ', r; split; auto.
        - simpl; f_equal; auto.
        - eq goal H2; do 2 f_equal; simpl; lia.
  Qed.

  Notation "Σ //ₙ a ⊕ b ⊦ u" := (ndmm2_accept Σ a b u) (at level 70, no associativity).

  Notation "ρ //ₐ s -1> t" := (mma_sss ρ s t) (at level 70, no associativity).
  Notation "P //ₐ r :1> s" := (sss_step (@mma_sss _) P r s)  (at level 70, no associativity).
  Notation "P //ₐ s ->> t" := (sss_compute (@mma_sss _) P s t) (at level 70, no associativity).
  Notation "P //ₐ s ~~> t" := (sss_output (@mma_sss _) P s t) (at level 70, no associativity).

  Tactic Notation "state" "rebuild" ident(s) hyp(i) hyp(a) hyp(b) :=
    set (s := (i,a##b##ø));
    change a with (vec_pos (snd s) pos0);
    change b with (vec_pos (snd s) pos1);
    change i with (fst s).

  Hint Resolve in_eq in_cons : core.

  Local Fact mma2_instr_enc_sound Σ ρ i a b j a' b' : 
          ρ //ₐ (i,a##b##ø) -1> (j,a'##b'##ø) 
       -> ⟨i,ρ⟩₁ ⊆ Σ 
       -> Σ //ₙ a' ⊕ b' ⊦ j 
       -> Σ //ₙ a  ⊕ b  ⊦ i.
  Proof.
    state rebuild s1 i a b.
    state rebuild s2 j a' b'.
    generalize s1 s2; clear s1 s2 i a b j a' b'.
    destruct 1 as [ i x v | i x k v Hv | i x k v u Hv ]; try revert Hv;
      vec2 v into a b; repeat invert pos x; simpl.
    + constructor 2 with (1+i); auto.
    + constructor 3 with (1+i); auto.
    + intros -> ?; constructor 6 with (1+i); auto.
    + intros -> ?; constructor 7 with (1+i); auto.
    + intros -> ?; constructor 4 with k; auto.
    + intros -> ?; constructor 5 with k; auto.
  Qed.

  Local Fact mma2_step_linstr_sound Σ P i a b j a' b' : 
          (1,P) //ₐ (i,a##b##ø) :1> (j,a'##b'##ø) 
       -> ⟪1,P⟫ₗ ⊆  Σ 
       -> Σ //ₙ a' ⊕ b' ⊦ j 
       -> Σ //ₙ a  ⊕ b  ⊦ i.
  Proof.
    intros (n & L & ρ & R & v & H1 & H2 & H3).
    inversion H1; subst n P; clear H1.
    inversion H2; subst v i; clear H2.
    intros H. 
    apply mma2_instr_enc_sound with (1 := H3).
    apply incl_tran with (2 := H).
    rewrite mma2_linstr_enc_app; simpl.
    rewrite plus_comm.
    apply incl_appr, incl_appl, incl_refl.
  Qed.

  Variable P : list (mm_instr (pos 2)).

  Definition mma2_prog_enc := STOPₙ 0 :: ⟪1,P⟫ₗ.
  Notation ΣP := mma2_prog_enc.

  Local Lemma mma2_compute_linstr_sound i a b j a' b'  : 
          (1,P) //ₐ (i,a##b##ø) ->> (j,a'##b'##ø)
       -> ΣP //ₙ a' ⊕ b' ⊦ j 
       -> ΣP //ₙ a  ⊕ b  ⊦ i.
  Proof.
    intros (n & Hn); revert Hn.
    state rebuild s1 i a b.
    state rebuild s2 j a' b'.
    generalize s1 s2; clear s1 s2 i a b j a' b'.
    induction 1 as [ (i,v) | n (i,u) (j,v) (k,w) H1 H2 IH2 ]; simpl; auto.
    revert H1 H2 IH2; vec2 u into au bu; vec2 v into av bv; vec2 w into aw bw.
    simpl; intros H1 H2 IH3 H; generalize (IH3 H).
    apply mma2_step_linstr_sound with (1 := H1), incl_tl, incl_refl.
  Qed. 
 
  Local Lemma mma2_prog_enc_stop : ΣP //ₙ 0 ⊕ 0 ⊦ 0.
  Proof. constructor 1; simpl; auto. Qed.

  Hint Resolve mma2_prog_enc_stop : core.

  Local Lemma mma2_prog_enc_sound i a b  : 
          (1,P) //ₐ (i,a##b##ø) ->> (0,0##0##ø) -> ΣP //ₙ a  ⊕ b  ⊦ i.
  Proof. intros H; apply mma2_compute_linstr_sound in H; auto. Qed.

  Local Lemma mma2_prog_enc_complete a b i : 
             ΣP //ₙ a ⊕ b ⊦ i -> (1,P) //ₐ (i,a##b##ø) ->> (0,0##0##ø).
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
          as (l & [ x | x ] & r & H1 & H2); repeat invert pos x; simpl in H2.
        1-2: now destruct H2.
        1-2: now destruct H2 as [ | [] ].
    + destruct H as [ H | H ]; try discriminate.
      apply mma2_linstr_enc_In in H
        as (l & [ x | x ] & r & H3 & H2); repeat invert pos x; simpl in H2.
      2: now destruct H2.
      2-3: now destruct H2 as [ | [] ].
      destruct H2 as [ H2 | [] ]; inversion H2; subst.
      apply sss_compute_trans with (2 := IH1).
      rewrite H3.
      mma sss INC with pos0.
      mma sss stop.
    + destruct H as [ H | H ]; try discriminate.
      apply mma2_linstr_enc_In in H
        as (l & [ x | x ] & r & H3 & H2); repeat invert pos x; simpl in H2.
      1: now destruct H2.
      2-3: now destruct H2 as [ | [] ].
      destruct H2 as [ H2 | [] ]; inversion H2; subst.
      apply sss_compute_trans with (2 := IH1).
      rewrite H3.
      mma sss INC with pos1.
      mma sss stop.
    + destruct H as [ H | H ]; try discriminate.
      apply mma2_linstr_enc_In in H
        as (l & [ x | x ] & r & H3 & H2); repeat invert pos x; simpl in H2.
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
        as (l & [ x | x ] & r & H3 & H2); repeat invert pos x; simpl in H2.
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
        as (l & [ x | x j ] & r & H3 & H2); repeat invert pos x; simpl in H2.
      1-2: now destruct H2.
      2: now destruct H2 as [ | [] ].
      destruct H2 as [ H2 | [ H2 | [] ] ].
      1: easy.
      inversion H2; subst.
      apply sss_compute_trans with (2 := IH1).
      rewrite H3.
      mma sss DEC zero with pos0 j.
      mma sss stop.
    + destruct H as [ H | H ]; try discriminate.
      apply mma2_linstr_enc_In in H
        as (l & [ x | x j ] & r & H3 & H2); repeat invert pos x; simpl in H2.
      1-2: now destruct H2.
      1: now destruct H2 as [ | [] ].
      destruct H2 as [ H2 | [ H2 | [] ] ].
      1: easy.
      inversion H2; subst.
      apply sss_compute_trans with (2 := IH1).
      rewrite H3.
      mma sss DEC zero with pos1 j.
      mma sss stop.
  Qed.

  Theorem MMA2_ndMM2_equiv a b : (1,P) //ₐ (1,a##b##ø) ~~> (0,0##0##ø) 
                             <-> ΣP //ₙ a ⊕ b ⊦ 1.
  Proof.
    split.
    + intros []; apply mma2_prog_enc_sound; auto.
    + split.
      * now apply mma2_prog_enc_complete.
      * simpl; lia.
  Qed.

End MMA2_ndMM2.

Theorem reduction : MMA2_HALTS_ON_ZERO ⪯ @ndMM2_ACCEPT nat.
Proof.
  apply reduces_dependent; exists.
  intros (P & v); vec2 v into a b. 
  exists (existT _ (mma2_prog_enc P) (1,(a,b))).
  apply MMA2_ndMM2_equiv.
Qed.
