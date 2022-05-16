From Undecidability.FOL Require Import Semantics.FiniteTarski.Full.
From Undecidability.FOL Require Import Syntax.Facts Semantics.Tarski.FullFacts Syntax.BinSig.
From Undecidability.SeparationLogic Require Import MSL.

From Undecidability Require Import Shared.ListAutomation.
Import ListAutomationNotations.

From Undecidability.Shared Require Import Dec.
Require Import Undecidability.Synthetic.DecidabilityFacts.

Set Default Goal Selector "!".
Set Default Proof Using "Type".



(** encoding function following Cacagno, Yang, O'Hearn (2001) **)

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
  mand (mex (mpointer (Some 0) None None)) (encode phi).



(** backwards direction **)

Lemma map_hd X Y n (f : X -> Y) (v : Vector.t X (S n)) :
  Vector.hd (Vector.map f v) = f (Vector.hd v).
Proof.
  now apply (Vector.caseS' v).
Qed.

Lemma map_tl X Y n (f : X -> Y) (v : Vector.t X (S n)) :
  Vector.tl (Vector.map f v) = Vector.map f (Vector.tl v).
Proof.
  now apply (Vector.caseS' v).
Qed.

Lemma in_hd X n (v : Vector.t X (S n)) :
  Vector.In (Vector.hd v) v.
Proof.
  apply (Vector.caseS' v).
  intros. constructor.
Qed.

Lemma in_hd_tl X n (v : Vector.t X (S (S n))) :
  Vector.In (Vector.hd (Vector.tl v)) v.
Proof.
  apply (Vector.caseS' v). intros ? w.
  apply (Vector.caseS' w).
  constructor. constructor.
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

Lemma to_list_in' X n (v : Vector.t X n) x :
  x el Vector.to_list v -> Vector.In x v.
Proof.
  induction v; cbn.
  - inversion 1.
  - inversion 1; subst; try now left. right. apply IHv, H0.
Qed.

Section Backwards.

  Definition squash P {d : dec P} :=
    if Dec P then True else False.

  Arguments squash _ {_}.

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

  Lemma dom_eq h (x y : dom h) :
    proj1_sig x = proj1_sig y -> x = y.
  Proof.
    destruct x as [x Hx], y as [y Hy]; cbn.
    intros ->. f_equal. apply squash_pure.
  Qed.
  Arguments env _ _ _ _ : clear implicits.
  Lemma update_stack_cons s h d0 d x :
    (d .: env s h d0) x = env (update_stack s (Some (proj1_sig d))) h d0 x.
  Proof.
    destruct x as [|x]; try reflexivity. cbn. destruct Dec.
    - destruct d. now apply dom_eq.
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

  (* requirements *)

  Definition dom_cons {h} {a} :
    dom h -> dom (a::h).
  Proof.
    intros [x Hx]. exists x. apply squash_iff. right. now eapply squash_iff.
  Defined.

  Definition dom_list_cons {h} {a} (L : list (dom h)) :=
    map (@dom_cons h a) L. 

  Program Fixpoint dom_list h : list (dom h) :=
    match h with
    | nil => nil
    | (l, (None, None))::h => (exist _ l _) :: (dom_list_cons (dom_list h))
    | _::h => (dom_list_cons (dom_list h))
    end.
  Next Obligation.
    apply squash_iff. now left.
  Qed.

  Lemma dom_listable h :
    listable (dom h).
  Proof.
    exists (dom_list h). intros x.
    induction h as [|[l[[l1|][l2|]]]]; cbn.
    - destruct x as [x Hx]. apply squash_iff in Hx. apply Hx.
    - destruct x as [x Hx]. pose proof (proj1 (squash_iff _) Hx) as [H|H]; try discriminate.
      apply in_map_iff. exists (loc2dom H). split; try apply IHh. now apply dom_eq.
    - destruct x as [x Hx]. pose proof (proj1 (squash_iff _) Hx) as [H|H]; try discriminate.
      apply in_map_iff. exists (loc2dom H). split; try apply IHh. now apply dom_eq.
    - destruct x as [x Hx]. pose proof (proj1 (squash_iff _) Hx) as [H|H]; try discriminate.
      apply in_map_iff. exists (loc2dom H). split; try apply IHh. now apply dom_eq.
    - destruct x as [x Hx]. pose proof (proj1 (squash_iff _) Hx) as [H|H].
      + left. apply dom_eq. cbn. congruence.
      + right. apply in_map_iff. exists (loc2dom H). split; try apply IHh. now apply dom_eq.
  Qed.

  Lemma dom_discrete h :
    discrete (dom h).
  Proof.
    apply discrete_iff. constructor. intros [x Hx] [y Hy]. decide (x = y) as [H|H].
    - left. now apply dom_eq.
    - right. now intros [=].
  Qed.

  Lemma pairlist_dec X Y (L : list (X * Y)) y :
    eq_dec X -> eq_dec Y -> dec (exists x, (x, y) el L).
  Proof.
    intros DX DY. induction L as [|[a b]].
    - right. firstorder.
    - destruct IHL as [H|H].
      + left. destruct H as [x Hx]. exists x. now right.
      + decide (y = b) as [->|Hy].
        * left. exists a. now left.
        * right. intros [x[Hx|Hx]].
          -- apply Hy. congruence.
          -- apply H. now exists x.
  Qed.

  Lemma model_dec (h : heap) :
    decidable (fun v => i_atom (interp:=model h) (P:=tt) v).
  Proof.
    apply decidable_iff. constructor. intros v. cbn.
    apply pairlist_dec; eauto.
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
    enc_npair (enc_point d) (enc_point e) + S (length LD).

  Definition interp2heap : heap :=
    [(enc_point d, (None, None)) | d ∈ LD]
      ++ [(enc_pair d e, (Some (enc_point d), Some (enc_point e))) | (d, e) ∈ filter f (LD × LD)].

  Definition env2stack (rho : nat -> D) : stack :=
    fun n => Some (enc_point (rho n)).

  Lemma pos_inj L d e :
    d el L -> e el L -> pos L d = pos L e -> d = e.
  Proof.
    induction L; cbn; try tauto. intros [->|Hd] [->|He].
    all: repeat destruct Dec; try tauto; try congruence.
    intros [=]. auto.
  Qed.

  Lemma enc_point_inj d e :
    enc_point d = enc_point e -> d = e.
  Proof using LD_ex.
    apply pos_inj; apply LD_ex.
  Qed.

  Lemma sp_eval_ext s s' E :
    (forall n, s n = s' n) -> sp_eval s E = sp_eval s' E.
  Proof.
    intros HS. destruct E as [x|]; cbn; auto.
  Qed.

  Lemma msp_sat_ext s s' h P :
    (forall n, s n = s' n) -> msp_sat s h P <-> msp_sat s' h P.
  Proof.
    induction P in s, s' |- *; intros HS; cbn.
    - now setoid_rewrite (sp_eval_ext _ HS).
    - tauto.
    - now rewrite (IHP1 s s'), (IHP2 s s').
    - now rewrite (IHP1 s s'), (IHP2 s s').
    - now rewrite (IHP1 s s'), (IHP2 s s').
    - split; intros H v. all: eapply IHP; try apply (H v). all: intros []; cbn; auto.
    - split; intros [v H]; exists v. all: eapply IHP; try apply H. all: intros []; cbn; auto.
  Qed.

  Lemma reduction_forwards rho phi :
    rho ⊨ phi <-> msp_sat (env2stack rho) interp2heap (encode phi).
  Proof using LD_ex f_dec.
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

  (* requirements *)

  Lemma pos_bound L x :
    pos L x < S (length L).
  Proof.
    induction L; cbn.
    - lia.
    - decide (x = a); lia.
  Qed.

  Lemma enc_point_pair d d1 d2 :
    enc_point d <> enc_pair d1 d2.
  Proof.
    unfold enc_pair. assert (H : enc_point d < S (length LD)) by apply pos_bound. lia.
  Qed.

  Definition next xy : nat * nat :=
    match xy with
    | (0,y) => (S y, 0)
    | (S x, y) => (x, S y)
    end.

  Fixpoint decode n : nat * nat :=
    match n with
    | 0 => (0,0)
    | S n' => next (decode n')
    end.

  Fact decode_encode x y :
    decode (enc_npair x y) = (x, y).
  Proof.
    revert x y.
    enough (forall n x y, enc_npair x y = n -> decode n = (x, y)) by eauto.
    induction n as [|n IH]; intros x y; cbn.
    - destruct x, y; cbn.
      1: reflexivity. all: intros [=].
    - destruct y; cbn.
      + destruct x; cbn.
        * intros [=].
        * intros [= <-].
          rewrite (IH 0 x). 1: reflexivity.
          unfold enc_npair. replace (x + 0) with x by lia. reflexivity.
      + intros [= <-].
        rewrite (IH (S x) y). 1: reflexivity.
        unfold enc_npair. replace (y + S x) with (S y + x) by lia. reflexivity.
  Qed.

  Lemma enc_npair_inj n n' k k' :
    enc_npair n n' = enc_npair k k' -> (n, n') = (k, k').
  Proof.
    intros H. rewrite <- (decode_encode n n'), <- (decode_encode k k'). congruence.
  Qed.

  Lemma enc_pair_inj d d' e e' :
    enc_pair d d' = enc_pair e e' -> d = e /\ d' = e'.
  Proof using LD_ex.
    intros H. assert (((enc_point d), (enc_point d')) = ((enc_point e), (enc_point e'))) as [=].
    - apply enc_npair_inj. unfold enc_pair in H. lia.
    - split; now apply enc_point_inj.
  Qed.

  Lemma interp2heap_fun :
    functional interp2heap.
  Proof using LD_ex.
    intros l p p' [H|H] % in_app_iff [H'|H'] % in_app_iff.
    all: apply in_map_iff in H as [d [H1 H2]].
    all: apply in_map_iff in H' as [d' [H3 H4]].
    - congruence.
    - destruct d' as [d1 d2]. exfalso. apply (@enc_point_pair d d1 d2). congruence.
    - destruct d as [d1 d2]. exfalso. apply (@enc_point_pair d' d1 d2). congruence.
    - destruct d, d', p, p'. injection H1. injection H3. intros. subst. repeat f_equal.
      + eapply (@enc_pair_inj d d0 d1 d2). congruence.
      + eapply (@enc_pair_inj d d0 d1 d2). congruence.
  Qed.

  Lemma guarded (d : D) :
    exists (v : val) (l : nat), v = Some l /\ (l, (None, None)) el interp2heap.
  Proof using LD_ex.
    exists (Some (enc_point d)), (enc_point d). split; trivial.
    apply in_app_iff. left. apply in_map_iff. exists d; auto.
  Qed.

End Forwards.



(** reduction theorem **)

Require Import Undecidability.Synthetic.Definitions.
Import Vector.VectorNotations.

Lemma vec_inv1 {X} (v : Vector.t X 1) :
  v = [Vector.hd v].
Proof.
  apply (Vector.caseS' v). intros ?.
  now apply Vector.case0.
Qed.

Lemma vec_inv2 {X} (v : Vector.t X 2) :
  v = [Vector.hd v; Vector.hd (Vector.tl v)].
Proof.
  apply (Vector.caseS' v). intros x w.
  apply (Vector.caseS' w). intros ?.
  now apply Vector.case0.
Qed.

Lemma discrete_nodup X (L : list X) :
  eq_dec X -> { L' | NoDup L' /\ L <<= L' }.
Proof.
  intros d. induction L.
  - exists nil. split; auto. apply NoDup_nil.
  - destruct IHL as (L' & H1 & H2). decide (a el L') as [H|H].
    + exists L'. split; trivial. intros b. cbn. firstorder congruence.
    + exists (cons a L'). split; try now apply NoDup_cons. auto.
Qed.

Theorem reduction' phi :
  FV phi <<= nil -> FSATd phi <-> MSLSAT (encode' phi).
Proof.
  intros HV. split.
  - intros (D & M & rho & [L HL] & [H2] % discrete_iff & [f H3] & H4).
    pose (f' (p : D * D) := let (d, e) := p in f ([d; e])).
    destruct (@discrete_nodup D L H2) as [L'[HL1 HL2]].
    assert (HL2' : forall x, x el L') by auto.
    assert (H3' : forall v, i_atom (P:=tt) v <-> f' (Vector.hd v, Vector.hd (Vector.tl v)) = true).
    { intros v. unfold decider, reflects in H3. now rewrite (H3 v), (vec_inv2 v) at 1. }
    exists (@env2stack D L' H2 rho), (@interp2heap D L' H2 f'). split.
    + now eapply interp2heap_fun.
    + cbn. split; try now eapply reduction_forwards. apply guarded; trivial. exact (rho 0).
  - intros (s & h & _ & H). cbn in H. destruct H as [H' H]. destruct H' as (v & l & -> & Hl).
    exists (dom h), (model h), (@env s h (loc2dom Hl)). repeat split.
    + apply dom_listable.
    + apply dom_discrete.
    + intros [ ]. apply model_dec.
    + apply reduction_backwards; trivial. setoid_rewrite HV. intros x [].
Qed.

Lemma bounded_FV_term t n :
  bounded_t n t -> FV_term t < n.
Proof.
  induction 1; try destruct f; cbn. assumption.
Qed.

Lemma bounded_FV phi n :
  bounded n phi -> FV phi <<= seq 0 n.
Proof.
  induction 1; cbn.
  - intros x [t [<- Ht]] % in_map_iff.
    apply to_list_in', H, bounded_FV_term in Ht.
    apply in_seq. lia.
  - auto.
  - intros x [t [<- Ht]] % in_map_iff. apply in_filter_iff in Ht as [H1 H2].
    destruct t; try discriminate. apply IHbounded, in_seq in H1.
    cbn. apply in_seq. lia.
  - auto.
Qed.

Theorem reduction :
  FSATdc ⪯ MSLSAT.
Proof.
  exists (fun phi => encode' (proj1_sig phi)). intros [phi H]; unfold FSATdc; cbn.
  apply reduction'. change nil with (seq 0 0). now apply bounded_FV.
Qed.
