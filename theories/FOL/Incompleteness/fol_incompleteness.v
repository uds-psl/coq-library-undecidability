From Undecidability.Shared Require Import embed_nat Dec.
From Undecidability.Synthetic Require Import Definitions EnumerabilityFacts.

From Undecidability.FOL Require Import FullSyntax Axiomatisations.
From Undecidability.FOL.Arithmetics Require Import Signature Robinson NatModel.

From Undecidability.FOL.Incompleteness Require Import utils fol qdec bin_qdec sigma1 epf epf_mu formal_systems abstract_incompleteness ctq.
From Undecidability.FOL.Proofmode Require Import Theories ProofMode.

Require Import Lia String List.
Import ListNotations.

(** * Incompleteness of first-order logic *)

(* first-order logic with an enumerable theory is a formal system *)
Section fol_fs.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.
  Hypothesis (p : peirce).

  Definition fol_fs (T : theory) (Tenum : enumerable T) (Tconsis : ~T ⊢T ⊥) : FS form (fun φ => ¬φ).
  Proof.
    apply mkFS with (fprv := fun φ => T ⊢T φ).
    - apply enumerable_semi_decidable.
      + apply form_discrete.
      + unshelve eapply tprv_enumerable.
        * apply enumerable_PA_funcs.
        * apply enumerable_PA_preds.
        * assumption.
    - intros φ [T1 [HT1 H1]] [T2 [HT2 H2]]. apply Tconsis. exists (T1 ++ T2). split.
      + intros ψ [?|?]%in_app_or; auto.
      + eapply IE.
        * eapply Weak; first apply H2.
          apply incl_appr, incl_refl.
        * eapply Weak; first apply H1.
          apply incl_appl, incl_refl.
  Defined.
End fol_fs.


Section fol.
  Existing Instance PA_funcs_signature.
  Existing Instance PA_preds_signature.


  (** ** Q is essentially incomplete and essentially undecidable *)

  (* Any theory that strongly separates two recursively inseparable predicates is incompelte *)
  Section incomplete_strong_repr.
    Hypothesis (p : peirce).

    Variable theta : nat -> nat -\ bool.
    Hypothesis theta_universal : is_universal theta.

    Variable T : theory.
    Hypothesis Tenum : enumerable T.
    Hypothesis Tconsis : ~T ⊢T ⊥.

    Variable T' : theory.
    Hypothesis T'_T : T' ⊑ T.
    Hypothesis T'enum : enumerable T'.

    Variable r : nat -> form.
    Hypothesis Hrepr : 
      (forall c, theta c c ▷ true -> T' ⊢T r c) /\
      (forall c, theta c c ▷ false -> T' ⊢T ¬r c).

    Lemma fol_undecidable_strong_repr : ~decidable (fun s => T ⊢T s).
    Proof.
      assert (~T' ⊢T ⊥) as T'consis.
      { contradict Tconsis. now eapply WeakT. }
      eapply (insep_essential_undecidability) with (theta := theta) (fs := fol_fs Tenum Tconsis) (fs' := fol_fs T'enum T'consis).
      - assumption.
      - unfold extension. cbn. intros φ Hφ. now eapply WeakT.
      - exact Hrepr.
    Qed.

    Lemma fol_incomplete_strong_repr : exists n, ~T ⊢T r n /\ ~T ⊢T ¬r n.
    Proof.
      assert (~T' ⊢T ⊥) as T'consis.
      { contradict Tconsis. now eapply WeakT. }
      apply (insep_essential_incompleteness) with (theta := theta) (fs := fol_fs Tenum Tconsis) (fs' := fol_fs T'enum T'consis).
      - assumption.
      - unfold extension. cbn. intros φ Hφ. now eapply WeakT.
      - assumption.
    Qed.

  End incomplete_strong_repr.






  (* Q is essentially incomplete and essentially undecidable *)
  Section Q_incomplete.
    (* Hypothesis mu_universal : is_universal theta_mu. *)

    Hypothesis (p : peirce).
    Hypothesis ctq : @CTQ p.

    Variable T : theory.
    Hypothesis T_Q : list_theory Qeq ⊑ T.
    Hypothesis Tenum : enumerable T.
    Hypothesis Tconsis : ~@tprv _ _ _ p T ⊥.

    Theorem Q_undecidable : ~decidable (@tprv _ _ _ p T).
    Proof.
      assert (exists theta : nat -> nat -\ bool, is_universal theta) as [theta theta_universal].
      { apply epf_nat_bool, ctq_epfn, ctq. }
      assert (forall c, theta c c ▷ true -> theta c c ▷ false -> False) as Hdisj.
      { intros c Ht Hf. enough (true = false) by discriminate. eapply part_functional; eassumption. }

      edestruct (ctq_strong_sepr ctq Hdisj) as (ψ & Hb & HΣ & Hψ1 & Hψ2).
      1-2: apply theta_self_return_semi_decidable.
      eapply (@fol_undecidable_strong_repr p theta theta_universal T Tenum Tconsis (list_theory Qeq) T_Q (list_theory_enumerable Qeq)).
      instantiate (1 := fun c => ψ[(num c)..]).
      split; intros c H.
      - exists Qeq. eauto.
      - exists Qeq. eauto.
    Qed.

    Theorem Q_incomplete : exists φ, bounded 0 φ /\ Σ1 φ /\ ~@tprv _ _ _ p T φ /\ ~@tprv _ _ _ p T (¬φ).
    Proof. 
      assert (exists theta : nat -> nat -\ bool, is_universal theta) as [theta theta_universal].
      { apply epf_nat_bool, ctq_epfn, ctq. }
      assert (forall c, theta c c ▷ true -> theta c c ▷ false -> False) as Hdisj.
      { intros c Ht Hf. enough (true = false) by discriminate. eapply part_functional; eassumption. }

      edestruct (ctq_strong_sepr ctq Hdisj) as (ψ & Hb & HΣ & Hψ1 & Hψ2).
      1-2: apply theta_self_return_semi_decidable.
      edestruct (@fol_incomplete_strong_repr p theta theta_universal T Tenum Tconsis (list_theory Qeq) T_Q (list_theory_enumerable Qeq)).
      { instantiate (1 := fun c => ψ[(num c)..]).
        split; intros c H.
        - exists Qeq. eauto.
        - exists Qeq. eauto. }
      cbn in H. exists ψ[(num x)..]. 
      repeat apply conj.
      - eapply subst_bounded_max; last eassumption. intros [|n] Hn; last lia. apply num_bound.
      - now apply Σ1_subst.
      - apply H.
      - apply H.
    Qed.

  End Q_incomplete.

End fol.


Check Q_incomplete.
