From Undecidability.L Require Export L Tactics.LTactics Computability.Seval.
Require Import Coq.Logic.ConstructiveEpsilon.

Definition cChoice := constructive_indefinite_ground_description_nat_Acc.

Lemma enc_extinj {X} {R} {H:@encInj X R} (m n:X) : enc m == enc n -> m = n.
Proof.
  intros eq. apply unique_normal_forms in eq; try Lproc. now apply inj_enc.
Qed.

Lemma lcomp_comp Y {Ry:encodable Y} (u:term) (g: term -> Y):
  (forall x (y:Y), enc y = x -> y = g x) ->
  (exists y:Y, u == enc y) -> {y:Y| u == enc y}.
Proof.
  intros Hg Hu.
  assert (exists n (y:Y), eva n u = Some (enc y)).
  {
    destruct Hu as [y Hy]. apply equiv_lambda in Hy;try Lproc.
    assert (eval (u) (enc y)). split. assumption. Lproc.
    apply eval_seval in H. destruct H as [n Hn]. exists n. exists y. now apply seval_eva.
  }
  eapply cChoice in H. destruct H as [n H].
  destruct (eva n u) as [t|] eqn:Heva.
  -exists (g t). destruct H as [y H]. rewrite <- Heva in H. apply eva_equiv in H.
   assert (lambda t)by now apply eva_lam in Heva. apply eva_equiv in Heva. rewrite Heva in H. erewrite <- Hg. apply equiv_lambda in Heva;try Lproc. rewrite Heva. exact H. apply unique_normal_forms in H;try Lproc. congruence. 
  -exists (g #0). destruct H as [? H]. inv H.
  -intros n. destruct (eva n u) eqn:eq.
   +left. destruct H as [n' [y H]]. exists y. apply eva_equiv in H.
    assert (lambda t) by now apply eva_lam in eq. apply eva_equiv in eq. rewrite H in eq. apply unique_normal_forms in eq;[|Lproc..].  congruence.
   +right. intros [y eq']. congruence.
Qed.
