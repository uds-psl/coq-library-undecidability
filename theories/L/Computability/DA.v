From Undecidability.L.Computability Require Export Decidability Acceptability Enum EnumInt.

Theorem DA M : 
  ldec M -> lacc (fun _ => exists t, M t).
Proof.
  intros [u [lu H]].
  pose (P := lam ((u ((int g_inv)#0 )))). assert (pp:proc P) by (unfold P;Lproc).
  
  assert (dP:forall n : nat, exists b : bool, P (enc n) == enc b).
  { intros. destruct (H (g_inv n)) as [? [eq _]]. eexists. unfold P. Lsimpl. exact eq. }
  
  exists (lam (mu P)). split. Lproc. intros. split.
  -intros [m Hm]. edestruct (mu_complete pp). auto.
   +unfold P. redStep. Lrewrite. rewrite g_inv_g. destruct (H m) as [? [eq uM]]. destruct x;try tauto. exact eq. 
   +eapply Seval.eval_converges. Lsimpl. rewrite H0. Lsimpl.
  -intros [v [ R lv]]. LsimplHypo. edestruct (mu_sound pp) as [n [? [Pn Hn]]];eauto. subst.
   exists (g_inv n). unfold P in Pn. LsimplHypo. rewrite intApp,int_is_enc in Pn.  destruct (H (g_inv n)) as [[] [? ?]]. auto. rewrite Pn in H0. apply unique_normal_forms in H0; try Lproc. discriminate H0.
Qed.
