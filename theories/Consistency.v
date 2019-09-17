(** **** Consistency *)

From Undecidability.FOLC Require Export ND.

Section Consistency.
  Context {Sigma : Signature}.
  Context {HdF : eq_dec Funcs} {HdP : eq_dec Preds}.
  Context {HeF : enumT Funcs} {HeP : enumT Preds}.

  Definition consistent (T : theory) := ~ T ⊩CE ⊥.
  Definition consistent_max T := consistent T /\ forall f, consistent (T ⋄ f) -> f ∈ T.

  Lemma consistent_prv T phi :
    consistent T -> T ⊩CE phi -> consistent (T ⋄ phi).
  Proof.
    intros HT Hphi. intros Hpsi2. now apply HT, (prv_T_remove Hphi).
  Qed.

  Lemma consistency_inheritance T1 T2 :
    consistent T2 -> T1 ⊑ T2 -> consistent T1.
  Proof.
    intros H H2 H3. now eapply H, Weak_T, H2.
  Qed.

  Fact consistent_neg T phi :
    consistent T -> (¬ phi) ∈ T -> ~ phi ∈ T.
  Proof.
    intros HT H H2. apply HT.
    use_theory [phi; ¬ phi]. oapply 1. ctx.
  Qed.

  Fact consistent_neg2 T phi :
    consistent T -> (T ⋄ phi) ⊩CE ⊥ -> consistent (T ⋄ (¬ phi)).
  Proof.
    intros HT H. now apply consistent_prv, prv_T_impl.
  Qed.

  Fact consistent_max_out T phi :
    consistent_max T -> ~ phi ∈ T -> ~ consistent (T ⋄ phi).
  Proof.
    intros []; intuition.
  Qed.

  Lemma consistent_max_impl T phi psi :
    consistent_max T -> (phi --> psi ∈ T <-> (phi ∈ T -> psi ∈ T)).
  Proof.
    intros; split; destruct H as [H1 H2].
    - intros H H'. apply H2. apply consistent_prv; try assumption.
      use_theory [phi; phi --> psi]. oapply 1. ctx.

    - intros H. apply H2. intros (A & HA1 & HA2) % prv_T_impl.
      apply H1. apply (prv_T_remove (phi := psi)).
      + apply elem_prv, H, H2, consistent_prv. assumption. use_theory A.
        oindirect. oimport HA2. oapply 0. ointros. oexfalso. oapply 2. ctx.
      + use_theory (psi :: A). oimport HA2. oapply 0. ointros. ctx.
  Qed.

  Section Classical.
    Hypothesis XM : forall X, X \/ ~ X.
    Ltac indirect := match goal with
                      | [ |- ?H ] => destruct (XM H); [assumption | exfalso]
                    end.

    Lemma inconsistent T phi :
      ~ consistent (T ⋄ phi) -> T ⋄ phi ⊩CE ⊥.
    Proof.
      destruct (XM (T ⋄ phi ⊩CE ⊥)); tauto.
    Qed.

    Lemma consistent_max_out2 T phi :
      consistent_max T -> ~ phi ∈ T -> (¬ phi) ∈ T.
    Proof.
      intros [HT1 HT2] H2. now apply consistent_max_out, inconsistent, consistent_neg2, HT2 in H2.
    Qed.
  End Classical.
End Consistency.
