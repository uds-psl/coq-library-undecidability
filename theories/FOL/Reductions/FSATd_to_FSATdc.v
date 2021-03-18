From Undecidability.FOL Require Import FSAT.
From Undecidability.FOL.Util Require Import Syntax_facts FullTarski_facts sig_bin.
Require Import Undecidability.Synthetic.Definitions.
Require Import Vector Lia.

Definition exclosure phi : form :=
  let (N, _) := find_bounded phi in exist_times N phi.

Lemma exclosure_closed phi :
  bounded 0 (exclosure phi).
Proof.
  unfold exclosure. destruct find_bounded as [N HN]. now apply exists_close_form.
Qed.

Definition form2cform phi : cform :=
  exist _ (exclosure phi) (exclosure_closed phi).

Theorem reduction :
  FSATd ⪯ FSATdc.
Proof.
  exists form2cform. intros phi; unfold FSATdc; cbn.
  unfold exclosure. destruct find_bounded as [N HN].
  split; intros (D & M & rho & H1 & H2 & H3 & H4); exists D, M.
  - exists rho. repeat split; trivial. eapply subst_exist_sat; eauto.
  - apply subst_exist_sat2 in H4 as [sigma H]. exists sigma. repeat split; trivial.
Qed.
