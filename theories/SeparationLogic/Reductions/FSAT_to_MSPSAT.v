From Undecidability.FOL Require Import FSAT.
From Undecidability.FOL.Util Require Import Syntax_facts FullTarski_facts sig_bin.
Export Undecidability.FOL.Util.Syntax.FullSyntax.
From Undecidability.SeparationLogic Require Import min_seplogic.

From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.

From Undecidability.Shared Require Import Dec.
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

Lemma pointers_disc :
  eq_dec (nat * (val * val)).
Proof.
  exact _.
Qed.

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
  | quant q phi => map pred (filter (fun n : nat => if n then false else true) (FV phi))
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



(** reduction theorem **)

Require Import Undecidability.Synthetic.Definitions.

Theorem reduction :
  FSAT ⪯ MSPSAT.
Proof.
  exists encode'.
Admitted.
