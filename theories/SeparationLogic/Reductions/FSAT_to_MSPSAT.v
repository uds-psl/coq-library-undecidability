From Undecidability.FOL Require Import FSAT.
From Undecidability.FOL.Util Require Import Syntax_facts FullTarski_facts sig_bin.
Export Undecidability.FOL.Util.Syntax.FullSyntax.
From Undecidability.SeparationLogic Require Import min_seplogic.

From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.

From Undecidability.Shared Require Import Dec.
Require Import Undecidability.Synthetic.DecidabilityFacts.
From Equations Require Import Equations.



(** encoding function **)

Fixpoint encode {ff : falsity_flag} (phi : form) : msp_form :=
  match phi with
  | falsity => mbot
  | atom _ v => let x := match Vector.hd v with var x => x | func f _ => match f with end end in
               let y := match Vector.hd (Vector.tl v) with var y => y | func f _ => match f with end end in
               mand (mex (mpointer (Some 0) (Some (S x)) (Some (S y))))
                    (mand (mpointer (Some x) None None) ((mpointer (Some y) None None)))
  | bin Impl phi psi => mimp (encode phi) (encode psi)
  | bin Conj phi psi => mand (encode phi) (encode psi)
  | bin Disj phi psi => mor (encode phi) (encode psi)
  | quant All phi => mall (mimp (mpointer (Some 0) None None) (encode phi))
  | quant Ex phi => mex (mand (mpointer (Some 0) None None) (encode phi))
  end.

Definition encode' (phi : form) : msp_form :=
  mimp (mex (mpointer (Some 0) None None)) (encode phi).



(** backwards direction **)

Lemma map_hd X Y n (f : X -> Y) (v : Vector.t X (S n)) :
  Vector.hd (Vector.map f v) = f (Vector.hd v).
Proof.
  dependent elimination v. reflexivity.
Qed.

Lemma map_tl X Y n (f : X -> Y) (v : Vector.t X (S n)) :
  Vector.tl (Vector.map f v) = Vector.map f (Vector.tl v).
Proof.
  dependent elimination v. reflexivity.
Qed.

Lemma in_hd X n (v : Vector.t X (S n)) :
  Vector.In (Vector.hd v) v.
Proof.
  dependent elimination v. constructor.
Qed.

Lemma in_hd_tl X n (v : Vector.t X (S (S n))) :
  Vector.In (Vector.hd (Vector.tl v)) v.
Proof.
  dependent elimination v. constructor. dependent elimination t. constructor.
Qed.

Definition FV_term (t : term) : nat :=
  match t with
  | $n => n
  | func f v => match f with end
  end.

Fixpoint FV {ff : falsity_flag} (phi : form) : list nat :=
  match phi with
  | falsity => nil
  | atom _ v => map FV_term (Vector.to_list v)
  | bin b phi psi => (FV phi) ++ (FV psi)
  | quant q phi => [pred p | p ∈ filter (fun n : nat => if n then false else true) (FV phi)]
  end.

Lemma to_list_in X n (v : Vector.t X n) x :
  Vector.In x v -> x el Vector.to_list v.
Proof.
  induction v; cbn.
  - inversion 1.
  - inversion 1; subst; try now left.
    apply Eqdep_dec.inj_pair2_eq_dec in H3 as <-; try decide equality.
    right. apply IHv, H2.
Qed.

Section Backwards.

  Definition squash P {d : dec P} :=
    if Dec P then True else False.

  Lemma squash_iff P (d : dec P) :
    squash P <-> P.
  Proof.
    unfold squash. destruct Dec; tauto.
  Qed.

  Lemma squash_pure P (d : dec P) (H H' : squash P) :
    H = H'.
  Proof.
    remember (squash P) as S. unfold squash in HeqS.
    destruct Dec in HeqS; subst; try tauto. now destruct H, H'.
  Qed.

  Definition dom (h : heap) : Type :=
    { l | squash ((l, (None, None)) el h) }.

  Definition loc2dom {h : heap} {l} :
    (l, (None, None)) el h -> dom h.
  Proof.
    intros H. exists l. abstract (now apply squash_iff).
  Defined.

  Definition env (s : stack) (h : heap) (d0 : dom h) :
    nat -> dom h.
  Proof.
    intros n. destruct (s n) as [l |].
    - decide ((l, (None, None)) el h).
      + exact (loc2dom i).
      + exact d0.
    - exact d0.
  Defined.

  Instance model h :
    interp (dom h).
  Proof.
    split.
    - intros [].
    - intros [] v. exact (exists l, (l, (Some (proj1_sig (Vector.hd v)), Some (proj1_sig (Vector.hd (Vector.tl v))))) el h).
  Defined.

  Lemma update_stack_cons s h d0 d x :
    (d .: env s h d0) x = env (update_stack s (Some (proj1_sig d))) h d0 x.
  Proof.
    destruct x as [|x]; try reflexivity. cbn. destruct Dec.
    - destruct d. unfold loc2dom. f_equal. apply squash_pure.
    - contradict n. eapply squash_iff, proj2_sig.
  Qed.

  Lemma reduction_backwards (s : stack) (h : heap) (d0 : dom h) phi :
    (forall x, x el FV phi -> exists l, s x = Some l /\ (l, (None, None)) el h) -> env s h d0 ⊨ phi <-> msp_sat s h (encode phi).
  Proof.
    induction phi in s |- *; try destruct P; try destruct b0; try destruct q; cbn; intros HV.
    - tauto.
    - rewrite map_tl, !map_hd. destruct (Vector.hd t) as [x|[]] eqn : Hx.
      destruct (Vector.hd (Vector.tl t)) as [y|[]] eqn : Hy. cbn. split.
      + intros [l Hl].
        destruct (HV x) as (l1 & H1 & H2).
        { apply in_map_iff. exists (Vector.hd t). split; try now rewrite Hx. apply to_list_in, in_hd. }
        destruct (HV y) as (l2 & H3 & H4).
        { apply in_map_iff. exists (Vector.hd (Vector.tl t)). split; try now rewrite Hy. apply to_list_in, in_hd_tl. }
        unfold env in Hl. rewrite H1, H3 in Hl. do 2 destruct Dec; try tauto. cbn in Hl. repeat split.
        * exists (Some l), l. split; trivial. now rewrite H1, H3.
        * now exists l1.
        * now exists l2.
     + intros [[v[l[-> Hl]]][[l1[H1 H2]][l2[H3 H4]]]]. exists l. unfold env. rewrite H1, H3.
       do 2 destruct Dec; try tauto. cbn. now rewrite <- H1, <- H3.
  - rewrite IHphi1, IHphi2; try tauto. all: intros x Hx; apply HV; apply in_app_iff; auto.
  - rewrite IHphi1, IHphi2; try tauto. all: intros x Hx; apply HV; apply in_app_iff; auto.
  - rewrite IHphi1, IHphi2; try tauto. all: intros x Hx; apply HV; apply in_app_iff; auto.
  - split; intros H.
    + intros [l|] [l'[H1 H2]]; try discriminate. injection H1. intros <-. apply IHphi.
      * intros [|x] Hx; try now exists l. apply HV. apply in_map_iff. exists (S x). split; trivial. now apply in_filter_iff.
      * eapply sat_ext; try apply (H (loc2dom H2)). intros x. now rewrite update_stack_cons.
    + intros [l Hl]. assert (Hl' : (l, (None, None)) el h) by now eapply squash_iff. eapply sat_ext, IHphi, H; cbn.
      * apply update_stack_cons.
      * intros [|x] Hx; try now exists l. apply HV. apply in_map_iff. exists (S x). split; trivial. now apply in_filter_iff.
      * exists l. split; trivial.
  - split; intros H.
    + destruct H as [[l Hl] H]. assert (Hl' : (l, (None, None)) el h) by now eapply squash_iff.
      exists (Some l). split; try now exists l. apply IHphi.
      * intros [|x] Hx; try now exists l. apply HV. apply in_map_iff. exists (S x). split; trivial. now apply in_filter_iff.
      * eapply sat_ext; try apply H. intros x. now rewrite update_stack_cons.
    + destruct H as [[l|][[l'[H1 H2]] H]]; try discriminate. injection H1. intros <-.
      exists (loc2dom H2). eapply sat_ext, IHphi, H.
      * intros x. now erewrite update_stack_cons.
      * intros [|x] Hx; try now exists l. apply HV. apply in_map_iff. exists (S x). split; trivial. now apply in_filter_iff.
  Qed.

End Backwards. 



(** forwards direction **)

Section Forwards.

  Variable D : Type.
  Variable I : interp D.

  Variable LD : list D.
  Hypothesis LD_ex : forall d, d el LD.
  Hypothesis LD_nodup : NoDup LD.

  Hypothesis D_disc : forall d e : D, dec (d = e).

  Variable f : D * D -> bool.
  Hypothesis f_dec : forall v, i_atom (P:=tt) v <-> f (Vector.hd v, (Vector.hd (Vector.tl v))) = true.

  Fixpoint pos L (d : D) : nat :=
    match L with
    | nil => 0
    | e::L => if Dec (d = e) then 0 else S (pos L d) 
    end.

  Definition enc_point (d : D) : nat :=
    pos LD d.

  Fixpoint sum n : nat :=
    match n with
    | 0 => 0
    | S n' => S n' + sum n'
    end.

  Definition enc_npair x y : nat :=
    y + sum (y + x).

  Definition enc_pair d e : nat :=
    enc_npair (enc_point d) (enc_point e) + length LD.

  Definition interp2heap : heap :=
    [(enc_point d, (None, None)) | d ∈ LD]
      ++ [(enc_pair d e, (Some (enc_point d), Some (enc_point e))) | (d, e) ∈ filter f (LD × LD)].

  Definition env2stack (rho : nat -> D) : stack :=
    fun n => Some (enc_point (rho n)).

  Lemma enc_point_inj d e :
    enc_point d = enc_point e -> d = e.
  Proof.
  Admitted.

  Lemma msp_sat_ext s s' h P :
    (forall n, s n = s' n) -> msp_sat s h P <-> msp_sat s' h P.
  Proof.
  Admitted.

  Lemma reduction_forwards rho phi :
    rho ⊨ phi <-> msp_sat (env2stack rho) interp2heap (encode phi).
  Proof.
    induction phi in rho |- *; try destruct P; try destruct b0; try destruct q; cbn.
    - tauto.
    - rewrite f_dec, map_tl, !map_hd.
      destruct (Vector.hd t) as [x|[]] eqn : Hx. destruct (Vector.hd (Vector.tl t)) as [y|[]] eqn : Hy.
      cbn. split.
      + pose (d := rho x). pose (e := rho y). intros H. repeat split.
        * exists (Some (enc_pair d e)), (enc_pair d e). split; trivial.
          apply in_app_iff. right. apply in_map_iff. exists (d, e). split; try reflexivity.
          apply in_filter_iff. split; trivial. apply in_prod_iff. split; apply LD_ex.
        * exists (enc_point d). split; trivial. apply in_app_iff. left. apply in_map_iff. exists d; auto.
        * exists (enc_point e). split; trivial. apply in_app_iff. left. apply in_map_iff. exists e; auto.
      + intros [[v[l[-> Hl]]] _].
        apply in_app_iff in Hl as [Hl|Hl].
        * apply in_map_iff in Hl as [d [H1 H2]]. discriminate.
        * apply in_map_iff in Hl as [[d e] [H1 H2]]. apply in_filter_iff in H2 as [_ H2].
          unfold env2stack in H1. injection H1. now intros -> % enc_point_inj -> % enc_point_inj _.
    - now rewrite IHphi1, IHphi2.
    - now rewrite IHphi1, IHphi2.
    - now rewrite IHphi1, IHphi2.
    - split; intros H.
      + intros [l|] [l'[H1 H2]]; try discriminate. injection H1. intros <-. clear H1.
        apply in_app_iff in H2 as [[d[[=] _]] % in_map_iff |[[][]] % in_map_iff]; try discriminate; subst.
        eapply msp_sat_ext; try apply IHphi, (H d). now intros [].
      + intros d. apply IHphi. eapply msp_sat_ext; try apply (H (Some (enc_point d))).
        * now intros [].
        * exists (enc_point d). split; trivial. apply in_app_iff. left. apply in_map_iff. exists d; auto.
    - split.
      + intros [d H]. exists (Some (enc_point d)). split.
        * exists (enc_point d). split; trivial. apply in_app_iff. left. apply in_map_iff. exists d; auto.
        * eapply msp_sat_ext; try apply IHphi, H. now intros [].
      + intros [v[[l [-> Hl]] H]].
        apply in_app_iff in Hl as [[d[[=] _]] % in_map_iff |[[][]] % in_map_iff]; try discriminate; subst.
        exists d. apply IHphi. eapply msp_sat_ext; try apply H. now intros [].
  Qed.

End Forwards.



(** reduction theorem **)

Require Import Undecidability.Synthetic.Definitions.

Theorem reduction :
  FSAT ⪯ MSPSAT.
Proof.
  exists encode'.
Admitted.
