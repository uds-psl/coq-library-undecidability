(* Enumeration Utils for Tarski Completeness *)

From Undecidability.FOL Require FragmentSyntax.
From Undecidability.Synthetic Require Import Definitions DecidabilityFacts MPFacts EnumerabilityFacts ListEnumerabilityFacts ReducibilityFacts.
From Undecidability Require Import Shared.ListAutomation Shared.Dec.
From Undecidability Require Import Shared.Libs.PSL.Vectors.Vectors Shared.Libs.PSL.Vectors.VectorForall.
Import ListAutomationNotations.
From FOL.Completeness Require Export TarskiConstructions.

Section Enumeration.

  Context {Σf : funcs_signature} {Σp : preds_signature}.
  Context {HdF : eq_dec Σf} {HdP : eq_dec Σp}.
  Variable eF : nat -> option Σf.
  Context {HeF : enumerator__T eF Σf}.
  Variable eP : nat -> option Σp.
  Context {HeP : enumerator__T eP Σp}.

  #[local] Hint Constructors bounded : core.


  Definition list_enum_to_enum {X} (L : nat -> list X) (n : nat) : option X :=
    let (n, m) := Cantor.of_nat n in nth_error (L n) m.

  Definition form_list_enum := (@L_form _ _ _
                                _ (enumerator__T_of_list HeF) _ (enumerator__T_of_list HeP)
                                _ enum_frag_logic_binop _ enum_frag_logic_quant).

  Definition form_list_enum_bounded {ff:falsity_flag} (n:nat) : list form := 
    (flat_map (fun f => if bounded_dec f n then [f] else []) (form_list_enum ff n)).

  Lemma form_list_is_enum {ff:falsity_flag} : list_enumerator__T (form_list_enum ff) _.
  Proof.
    apply enum_form.
  Qed.

  Lemma form_list_bounded_is_enum {ff:falsity_flag} : list_enumerator__T (@form_list_enum_bounded ff) _.
  Proof.
    intros f. destruct (form_list_is_enum f) as [m Hm].
    destruct (find_bounded f) as [m2 Hm2].
    exists (max m m2).
    unfold form_list_enum_bounded. eapply in_flat_map. exists f; split.
    - unfold form_list_enum. eapply cum_ge'. 1: apply L_form_cml. 1: apply Hm. lia.
    - destruct bounded_dec as [Hl|Hr]. 1:now left. exfalso. apply Hr. eapply bounded_up. 1: apply Hm2. lia.
  Qed.

  Definition form_enum_with_default {ff} d n := match list_enum_to_enum (@form_list_enum_bounded ff) n with Some k => k | _ => d end.

  Lemma form_default_is_enum {ff:falsity_flag} d : forall f, exists n, (@form_enum_with_default ff d n) = f.
  Proof.
    intros f. destruct (form_list_bounded_is_enum f) as [m Hm].
    unfold form_enum_with_default, list_enum_to_enum.
    destruct (In_nth_error _ _ Hm) as [n Hn].
    exists (Cantor.to_nat (m, n)). rewrite Cantor.cancel_of_to.
    rewrite Hn. easy.
  Qed.

  Lemma form_default_is_bounded {ff:falsity_flag} d : bounded 0 d -> forall n, bounded n (@form_enum_with_default ff d n).
  Proof.
    intros Hb n.
    unfold form_enum_with_default, list_enum_to_enum.
    destruct (Cantor.of_nat n) as [n' m'] eqn:Hn.
    pose proof (Cantor.to_nat_non_decreasing n' m'). rewrite <- Hn in H.
    rewrite Cantor.cancel_to_of in H.
    unfold form_list_enum_bounded.
    generalize (form_list_enum ff n'); intros l.
    destruct (nth_error _ _) as [k|] eqn:Heq.
    2: eapply bounded_up; [apply Hb|lia].
    apply nth_error_In in Heq.
    apply in_flat_map in Heq.
    destruct Heq as [x [Hx1 Hx2]].
    destruct (bounded_dec x n') as [Hbo|]. 2:easy.
    destruct Hx2 as [->|[]]. eapply bounded_up. 1: apply Hbo. lia.
  Qed.

  Section nat_inject.
    Fixpoint to_form (n:nat) : form := match n with
      0 => ⊥
    | S n => (⊥ → ⊥) → to_form n end.
    Fixpoint from_form (f:form) : option nat := match f with
      ⊥ => Some 0
    | bin Impl (bin Impl falsity falsity) x => match from_form x with Some n => Some (S n) | _ => None end
    | _ => None end.

    Lemma to_from_form f n : from_form f = Some n -> f = to_form n.
    Proof.
      revert n. induction f as [| |[] phi|] using form_ind_falsity; cbn; try congruence.
      - intros n Hn. assert (n=0) as -> by congruence. easy.
      - intros n. induction phi as [| |[] phi ? psi|]using form_ind_falsity; cbn; try congruence.
        induction phi using form_ind_falsity; cbn; try congruence.
        induction psi using form_ind_falsity; cbn; try congruence.
        destruct (from_form f1) eqn:Heq; cbn; try congruence.
        intros H. destruct n; cbn; try congruence.
        rewrite (IHf1 n); congruence.
    Qed.

    Lemma from_to_form n : from_form (to_form n) = Some n.
    Proof.
      induction n; cbn; now try rewrite IHn.
    Qed.

    Lemma to_form_closed n : closed (to_form n).
    Proof.
      induction n; cbn; unfold closed; eauto.
    Qed.

    Lemma to_form_contradictory n : [to_form n] ⊢C ⊥.
    Proof.
      induction n.
      - apply Ctx; now left.
      - apply (IE (phi := to_form n)).
        * apply II. eapply Weak. 1: apply IHn. intros x [<- | []]; now left.
        * eapply IE; [apply Ctx; now left|apply II, Ctx; now left].
    Qed.
  End nat_inject.

End Enumeration.