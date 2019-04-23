From Undecidability.L.Computability Require Import Por Acceptability Encoding Decidability.

Theorem AD M : (forall x, M x \/ ~ M x) -> lacc M -> lacc (complement M) -> ldec M.
Proof.
  intros pdec_M [u [[cls_u lam_u] Hu]] [v [[cls_v lam_v] Hv]].
  pose (por_u_v := lam (Por (((int app) (enc u) ((int (@enc term _)) #0)))
                            (((int app) (enc v) ((int (@enc term _)) #0))))).
  assert (proc por_u_v) by (subst por_u_v;Lproc).
  exists por_u_v.
  split. Lproc. intros t.
  unfold complement,pi in *. edestruct Por_correct_2 as [b H'].
  destruct (pdec_M t).
  -apply Por_correct_1a. rewrite <- Hu. eassumption. 
  -apply Por_correct_1b. rewrite <- Hv. eassumption.
  -exists b. unfold por_u_v. split. Lsimpl. exact H'.
   apply Por_correct' in H'. destruct b. now apply Hu. now apply Hv.
Qed.
