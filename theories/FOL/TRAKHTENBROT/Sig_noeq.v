(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia Relations.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.FOL.TRAKHTENBROT
  Require Import notations utils fol_ops fo_sig fo_terms 
                 fo_logic fo_congruence fo_sat.

Import fol_notations.

Set Implicit Arguments.

Local Infix "∊" := In (at level 70, no associativity).
Local Infix "⊑" := incl (at level 70, no associativity). 
Local Notation ø := vec_nil.

(* * FSATEQ reduces to FSAT *)

(* 1/ A is satisfiable in a fin/dec/interpreted model iff 
     f(A) if satisfiable in a fin/dec model

    2/ A is satisfiable in a fin/dec iff 
      f(A) if satisfiable in a fin/dec/interpreted model 

    for 2/ simply add an equality symbol that is not in A
    and do not use it and interpret it as =. f(A) is same
    as A but in an upgraded signature

    for 1/ A over Σ may contain an identity symbol e
    the idea ... given ls and lr containing the syms and rels
    belongs of A, and also e,  

    Of course if A is satisfiable interpreted that A is 
    satisfiable (uninterpreted). No suppose A is satisfiable
    uninterpreted, how can we ensure that e is interpreted
    by equality in the compressed model.

    For this we add formulas stating that e is a congruence
    for any on the symbols and rels in ls/lr so that in the
    compressed model, e will ensure bisimilarity and thus
    equality.

  *)

Section remove_interpreted_symbol.

  Variables (Σ : fo_signature) (ls : list (syms Σ)) (lr : list (rels Σ))
            (e : rels Σ) (H_ae : ar_rels _ e = 2) (He : e ∊ lr). 

  Notation 𝕋 := (fol_term Σ).
  Notation 𝔽 := (fol_form Σ).

  Notation "x ≡ y" := (@fol_atom Σ e (cast (x##y##ø) (eq_sym H_ae))) (at level 59).

  Definition Σ_noeq A := fol_congruence H_ae ls lr ⟑ A.

  Section soundness.

    Variable (A : 𝔽) (X : Type).

    Theorem Σ_noeq_sound : 
               fo_form_fin_dec_eq_SAT_in _ H_ae A X
            -> fo_form_fin_dec_SAT_in (Σ_noeq A) X.
    Proof.
      intros (M & H1 & H2 & HE & phi & H5).
      exists M, H1, H2, phi; unfold Σ_noeq.
      rewrite fol_sem_bin_fix; split; auto.
      rewrite fol_sem_congruence.
      split; [ | msplit 2 ].
      + split.
        * intros s _ v w H; rewrite HE.
          f_equal; apply vec_pos_ext; intros p.
          apply HE, H.
        * intros r _ v w H.
          apply fol_equiv_ext; f_equal.
          apply vec_pos_ext; intros p.
          apply HE, H.
      + intros ?; rewrite HE; auto.
      + intros ? ? ?; rewrite !HE; intros; subst; auto.
      + intros ? ?; rewrite !HE; intros; subst; auto.
    Qed.

  End soundness.

  Section completeness.

    (* Not sure how to make this one work over infinite models 
       Need some replacement for the quotient below *)

    Hint Resolve finite_t_pos : core.

    Variable (A : 𝔽) 
             (HA1 : fol_syms A ⊑ ls) 
             (HA2 : fol_rels A ⊑ lr).

    Theorem Σ_noeq_complete : 
               fo_form_fin_dec_SAT (Σ_noeq A)
            -> fo_form_fin_dec_eq_SAT e H_ae A.
    Proof using HA1 HA2.
      intros (X & M & H1 & H2 & phi & H5 & H3).
      apply fol_sem_congruence in H5
        as ((H4 & H5) & (H6 & H8 & H7)).
      set (R x y := fom_rels M e (cast (x ## y ## ø) (eq_sym H_ae))).
      destruct H1 as (lX & HlX).
      destruct decidable_EQUIV_fin_quotient with (l := lX) (R := R)
        as [ n cls repr G1 G2 ]; auto.
      + intros; apply H2.
      + intros x; exists x; split; auto; apply H6.
      + exists (pos n).
        set (Mn := Mk_fo_model Σ
               (fun s v => cls (fom_syms M s (vec_map repr v)))
               (fun r v => fom_rels M r (vec_map repr v))).
        exists Mn.
        exists; auto.
        exists. { intros r v; apply H2. }
        exists.
        { intros p q.
          unfold Mn; simpl.
          rewrite cast_fun; simpl.
          unfold R in G2; rewrite G2, !G1; tauto. }
        exists (fun n => cls (phi n)).
        revert H3.
        apply fo_model_projection' with (i := cls) (j := repr) (ls := ls) (lr := lr); auto.
        * intros s v Hs; simpl; apply G2.
          rewrite vec_map_map; red.
          apply H4; auto.
          intros p; rew vec; apply G2.
          rewrite G1; auto.
        * intros r v Hr; simpl.
          rewrite vec_map_map.
          apply H5; auto.
          intros p; rew vec; apply G2.
          rewrite G1; auto.
    Qed.

  End completeness.

End remove_interpreted_symbol.

