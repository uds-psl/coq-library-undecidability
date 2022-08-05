From Undecidability.FOL Require Import FullSyntax.
From Undecidability.FOL.Arithmetics Require Import Signature Robinson NatModel.

From Undecidability.FOL.Incompleteness Require Import utils fol qdec.
From Undecidability.FOL.Proofmode Require Import Theories ProofMode.

Require Import Lia.
Require Import String.


Open Scope string_scope.

Require Import Setoid.

Require Import Undecidability.Shared.Libs.DLW.Vec.vec.

Require Import String.
Open Scope string_scope.

Section bin_qdec.
  Existing Instance PA_preds_signature.
  Existing Instance PA_funcs_signature.
  Existing Instance interp_nat.

  Section lemmas.
    Context `{pei : peirce}.

    Lemma Q_add_assoc1 x y z t : Qeq ⊢ num t == (x ⊕ y) ⊕ z → num t == x ⊕ (y ⊕ z).
    Proof. 
      induction t as [|t IH] in x |-*; fstart; fintros "H".
      - fassert ax_cases as "C"; first ctx. 
        fdestruct ("C" x) as "[Hx|[x' Hx']]".
        + frewrite "H". frewrite "Hx".
          frewrite (ax_add_zero y). frewrite (ax_add_zero (y ⊕ z)).
          fapply ax_refl.
        + fexfalso. fapply (ax_zero_succ ((x' ⊕ y) ⊕ z)).
          frewrite <-(ax_add_rec z (x' ⊕ y)).
          frewrite <-(ax_add_rec y x').
          frewrite <-"Hx'". fapply "H".
      - fassert ax_cases as "C"; first ctx. 
        fdestruct ("C" x) as "[Hx|[x' Hx']]".
        + frewrite "H". frewrite "Hx".
          frewrite (ax_add_zero y). frewrite (ax_add_zero (y ⊕ z)).
          fapply ax_refl.
        + frewrite "Hx'". frewrite (ax_add_rec (y ⊕ z) x').
          specialize (IH x').
          fapply ax_succ_congr. fapply IH.
          fapply ax_succ_inj.
          frewrite <-(ax_add_rec z (x' ⊕ y)).
          frewrite <-(ax_add_rec y x').
          frewrite <-"Hx'". fapply "H".
    Qed.
    Lemma Q_add_assoc2 x y z t : Qeq ⊢ num t == (x ⊕ y) ⊕ z → num t == y ⊕ (x ⊕ z).
    Proof. 
      induction t as [|t IH] in x |-*; fstart; fintros "H".
      - fassert ax_cases as "C"; first ctx. 
        fdestruct ("C" x) as "[Hx|[x' Hx']]".
        + frewrite "H". frewrite "Hx".
          frewrite (ax_add_zero y). frewrite (ax_add_zero z).
          fapply ax_refl.
        + fexfalso. fapply (ax_zero_succ ((x' ⊕ y) ⊕ z)).
          frewrite <-(ax_add_rec z (x' ⊕ y)).
          frewrite <-(ax_add_rec y x').
          frewrite <-"Hx'". fapply "H".
      - fassert ax_cases as "C"; first ctx. 
        fdestruct ("C" x) as "[Hx|[x' Hx']]".
        + frewrite "H". frewrite "Hx".
          frewrite (ax_add_zero y). frewrite (ax_add_zero z).
          fapply ax_refl.
        + frewrite "Hx'". frewrite (ax_add_rec z x').
          Check add_rec_swap2.
          pose proof (add_rec_swap2 t y (x' ⊕ z)). cbn in H.
          fapply ax_sym. fapply H. fapply ax_sym.
          fapply IH.
          fapply ax_succ_inj.
          frewrite <-(ax_add_rec z (x' ⊕ y)).
          frewrite <-(ax_add_rec y x').
          frewrite <-"Hx'". fapply "H".
    Qed.

    Lemma bin_bounded_forall_iff t φ : bounded_t 0 t -> 
      Qeq ⊢ (∀∀ ($1 ⊕ $0 ⧀= t) → φ) ↔
            (∀ ($0 ⧀= t) → ∀ ($0 ⧀= t) → ($1 ⊕ $0 ⧀= t) → φ).
    Proof.
      intros Hb. destruct (closed_term_is_num Hb) as [t' Ht'].
      cbn. unfold "↑". 
      fstart. 
      fassert (t == num t') as "Ht" by fapply Ht'.
      fsplit.
      - fintros "H" x "Hx".
        fintros y "Hy" "Hxy".
        fapply "H". repeat rewrite (bounded_t_0_subst _ Hb). ctx.
      - fintros "H" x y. fintros "[z Hz]".
        fapply "H".
        + fexists (y ⊕ z). 
          rewrite !(bounded_t_0_subst _ Hb).
          frewrite "Ht". fapply Q_add_assoc1.
          feapply ax_trans.
          * feapply ax_sym. fapply "Ht".
          * fapply "Hz". 
        + fexists (x ⊕ z). 
          rewrite !(bounded_t_0_subst _ Hb).
          frewrite Ht'. fapply Q_add_assoc2.
          feapply ax_trans.
          * feapply ax_sym. fapply "Ht".
          * fapply "Hz".  
        + fexists z. ctx.
    Qed.
  End lemmas.


  Lemma Qdec_bin_bounded_forall t φ :
    Qdec φ -> Qdec (∀∀ $1 ⊕ $0 ⧀= t`[↑]`[↑] → φ).
  Proof.
    intros Hφ. 
    eapply (@Qdec_iff' (∀ ($0 ⧀= t`[↑]) → ∀ ($0 ⧀= t`[↑]`[↑]) → ($1 ⊕ $0 ⧀= t`[↑]`[↑]) → φ)).
    - intros ρ Hb.
      cbn. rewrite !PAle_subst. cbn. rewrite !up_term.
      unfold "↑".
      assert (bounded_t 0 t`[ρ]) as Ht.
      { destruct (find_bounded_t t) as [k Hk].
        eapply subst_bounded_max_t; last eassumption. auto. }
      pose proof (@bin_bounded_forall_iff intu t`[ρ] φ Ht).
      pose proof (subst_Weak ρ H) as H'. change (List.map _ _) with Qeq in H'.
      apply frewrite_equiv_switch. 
      cbn in H'. rewrite !PAle_subst in H'.
      rewrite !(bounded_t_0_subst _ Ht). rewrite !(bounded_t_0_subst _ Ht) in H'.
      apply H'.
    - do 2 apply Qdec_bounded_forall.
      apply Qdec_impl.
      + apply Qdec_le.
      + assumption.
  Qed.


End bin_qdec.
