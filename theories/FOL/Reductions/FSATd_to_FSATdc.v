From Undecidability.FOL Require Import FSAT.
From Undecidability.FOL.Util Require Import Syntax_facts FullTarski_facts sig_bin.
Require Import Undecidability.Synthetic.Definitions.
Require Import Vector Lia.

(* code copied from Util/FA_facts.v, should be moved to a more general place *)

Fixpoint iter {X: Type} f n (x : X) :=
  match n with
  | 0 => x
  | S m => f (iter f m x)
  end.

Fact iter_switch {X} f n x :
  f (@iter X f n x) = iter f n (f x).
Proof.
  induction n; cbn; now try rewrite IHn.
Qed.

Lemma bounded_S_exists N phi :
  bounded (S N) phi <-> bounded N (∃ phi).
Proof.
  split; intros H.
  - now constructor.
  - inversion H. apply inj_pair2_eq_dec' in H4 as ->; trivial.
    unfold Dec.dec. decide equality.
Qed.

Definition exist_times n (phi : form) := iter (fun psi => ∃ psi) n phi.

Section SEM.

  Context {D : Type}.
  Context {I : interp D}.
  
  Lemma bounded_eval_t n t sigma tau :
    (forall k, n > k -> sigma k = tau k) -> bounded_t n t -> eval sigma t = eval tau t.
  Proof.
    intros H. induction 1; cbn; auto.
    f_equal. now apply Vector.map_ext_in.
  Qed.
  
  Lemma bound_ext N phi rho sigma :
    bounded N phi -> (forall n, n < N -> rho n = sigma n) -> (rho ⊨ phi <-> sigma ⊨ phi).
  Proof.
    induction 1 in sigma, rho |- *; cbn; intros HN; try tauto.
    - enough (map (eval rho) v = map (eval sigma) v) as E. now setoid_rewrite E.
      apply Vector.map_ext_in. intros t Ht.
      eapply bounded_eval_t; try apply HN. now apply H.
    - destruct binop; now rewrite (IHbounded1 rho sigma), (IHbounded2 rho sigma).
    - destruct quantop.
      + split; intros Hd d; eapply IHbounded.
        all : try apply (Hd d); intros [] Hk; cbn; auto.
        symmetry. all: apply HN; lia.
      + split; intros [d Hd]; exists d; eapply IHbounded.
        all : try apply Hd; intros [] Hk; cbn; auto.
        symmetry. all: apply HN; lia.
  Qed.
  
  Corollary sat_closed rho sigma phi :
    bounded 0 phi -> rho ⊨ phi <-> sigma ⊨ phi.
  Proof.
    intros H. eapply bound_ext. apply H. lia.
  Qed.
  
  Lemma subst_exist_sat rho phi N :
    rho ⊨ phi -> bounded N phi -> forall rho, rho ⊨ (exist_times N phi).  
  Proof.
    induction N in phi, rho |-*; intros.
    - cbn. eapply sat_closed; eassumption.
    - cbn -[sat]. rewrite iter_switch. apply (IHN (S >> rho)).
      exists (rho 0). eapply sat_ext. 2: apply H.
      now intros [].
      now apply bounded_S_exists.
  Qed.

  Fact subst_exist_sat2 N : forall rho phi, rho ⊨ (exist_times N phi) -> (exists sigma, sigma ⊨ phi).
  Proof.
    induction N.
    - eauto.
    - intros rho phi [? H]. now apply IHN in H.
  Qed.

End SEM.

(* lemma copied from Reductions/H10p_to_FA.v, to be moved *)

Lemma exists_close_form N phi :
  bounded 0 (exist_times N phi) <-> bounded N phi.
Proof.
  induction N in phi |- *.
  - reflexivity.
  - cbn. rewrite iter_switch.
    change (iter _ _ _) with (exist_times N (∃ phi)).
    setoid_rewrite IHN. symmetry.
    now apply bounded_S_exists.
Qed.

(* actual reduction function *)

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
