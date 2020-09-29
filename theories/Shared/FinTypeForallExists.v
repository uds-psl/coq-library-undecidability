From PslBase Require Import FiniteTypes.

Lemma list_forall_exists (F : Type) (P : F -> nat -> Prop) L :
    (forall x n, P x n -> forall m, m >= n -> P x m) ->
    (forall x : F, x el L -> exists n, P x n) -> exists N, forall x, x el L -> P x N.
Proof.
    intros P_mono FE.
    induction L.
    - exists 0. intros ? [].
    - destruct IHL as [C HC].
      + intros; eapply FE. eauto.
      + destruct (FE a) as [c Hc]. eauto.
        exists (c + C). intros ? [-> | ].
        eapply P_mono. eassumption. lia. eapply P_mono. eapply HC. eauto. lia.
Qed.

Lemma fintype_forall_exists (F : finType) (P : F -> nat -> Prop) :
    (forall x n, P x n -> forall m, m >= n -> P x m) ->
    (forall x : F, exists n, P x n) -> exists N, forall x, P x N.
Proof.
    intros P_mono FE.
    destruct F as (X & l & Hl). cbn in *.
    destruct (@list_forall_exists X P l) as [C HC].
    - eassumption.
    - eauto.
    - exists C. intros x. eapply HC. eapply count_in_equiv. rewrite Hl. lia.
Qed.