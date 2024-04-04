Require Import List.
Import ListNotations.

Require Import Undecidability.PCP.PCP.
Require Import Undecidability.PCP.Util.Facts.
Import PCPListNotation.

From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts MoreEnumerabilityFacts ListEnumerabilityFacts.
From Undecidability Require Export PCP.PCP.
From Undecidability.Shared Require Export ListAutomation.
Import ListAutomationNotations ListAutomationHints.
Require Import Coq.Init.Wf.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat finite.


Set Implicit Arguments. 
Unset Strict Implicit.

Lemma tau1_app {X : Type} (A B: stack X) : tau1 (A ++ B) = tau1 A ++ tau1 B.
Proof.
  induction A; cbn; auto. destruct a. rewrite <- app_assoc. congruence.
Qed.

Lemma tau2_app {X : Type} (A B: stack X) : tau2 (A ++ B) = tau2 A ++ tau2 B.
Proof.
  induction A; cbn; auto. destruct a. rewrite <- app_assoc. congruence.
Qed.

Lemma tau1_inv (a : nat) B z :
tau1 B = a :: z ->
exists x y, (a :: x, y) el B.
Proof.
induction B; cbn; intros; inv H.
destruct a0 as ([],y).
- cbn in H1. firstorder.
- cbn in H1. inv H1. eauto.
Qed.

Lemma tau2_inv (a : nat) B z :
tau2 B = a :: z ->
exists x y, (y, a :: x) el B.
Proof.
induction B; cbn; intros; inv H.
destruct a0 as (x,[]).
- cbn in H1. firstorder.
- cbn in H1. inv H1. eauto.
Qed.

Definition cards {X : Type} (x: list X) := map (fun a => ([a], [a])) x.

Lemma tau1_cards {X : Type} (x: list X) : tau1 (cards x) = x.
Proof.
  induction x; cbv in *; try rewrite IHx; trivial.
Qed.

Lemma tau2_cards {X : Type} (x: list X) : tau2 (cards x) = x.
Proof.
  induction x; cbv in *; try rewrite IHx; trivial.
Qed.


Lemma itau1_app {X : Type} {P : stack X} A B : itau1 P (A++B) = itau1 P A ++ itau1 P B.
Proof. induction A; simpl; auto; rewrite <- app_assoc; simpl; f_equal; auto. Qed.

Lemma itau2_app {X : Type} {P : stack X} A B : itau2 P (A++B) = itau2 P A ++ itau2 P B.
Proof. induction A; simpl; auto; rewrite <- app_assoc; simpl; f_equal; auto. Qed.

Definition card_eq : forall x y : card bool, {x = y} + {x <> y}.
Proof.
  intros. repeat decide equality.
Defined.

Global Hint Rewrite (@tau1_app nat) (@tau2_app nat) (@tau1_cards nat) (@tau2_cards nat) : list.


Fixpoint sym (R : stack nat) :=
  match R with
    [] => []
  | (x, y) :: R => x ++ y ++ sym R
  end.

Lemma sym_app P R :
  sym (P ++ R) = sym P ++ sym R.
Proof.
  induction P as [ | [] ]; eauto; cbn; rewrite IHP. now rewrite <- ? app_assoc.
  Qed.

Lemma sym_map X (f : X -> card nat) l Sigma :
  (forall x : X, x el l -> sym [f x] <<= Sigma) -> sym (map f l) <<= Sigma.
Proof.
  intros. induction l as [ | ]; cbn in *.
  - firstorder.
  - pose proof (H a). destruct (f a). repeat eapply incl_app.
    + eapply app_incl_l, H0. eauto.
    + eapply app_incl_l, app_incl_R; eauto.
    + eauto.
  Qed. 

Lemma sym_word_l R u v  :
  (u, v) el R -> u <<= sym R.
Proof.
  induction R; cbn; intros.
  - tauto.
  - destruct a as (u', v'). destruct H.
    + inv H. intros x Hx. eapply in_app_iff. now left.
    + intros x Hx. rewrite ? in_app_iff. right. right. now eapply IHR.
  Qed.

Lemma sym_word_R R u v  :
  (u, v) el R -> v <<= sym R.
Proof.
  induction R; cbn; intros.
  - tauto.
  - destruct a as (u', v'). destruct H.
    + inv H. intros x Hx. rewrite ? in_app_iff. right. now left.
    + intros x Hx. rewrite ? in_app_iff. right. right. now eapply IHR.
  Qed.

#[export] Hint Resolve sym_word_l sym_word_R : core.

Lemma sym_mono A P :
  A <<= P -> sym A <<= sym P.
Proof.
  induction A as [ | (x,y) ]; cbn; intros.
  - firstorder.
  - eapply incl_app; try eapply incl_app. 
    + eapply sym_word_l. eapply H. now left.
    + eapply sym_word_R. eapply H. now left.
    + eapply IHA. eapply cons_incl. eassumption.
Qed.

Lemma tau1_sym A : tau1 A <<= sym A.
Proof.
  induction A as [ | (x & y) ].
  - firstorder.
  - cbn. intros ? [ | ] % in_app_iff. eapply in_app_iff. eauto.
    rewrite !in_app_iff. eauto.
Qed.

Lemma tau2_sym A : tau2 A <<= sym A.
Proof.
  induction A as [ | (x & y) ].
  - firstorder.
  - cbn. intros ? [ | ] % in_app_iff. rewrite ? in_app_iff. eauto.
    rewrite !in_app_iff. eauto.
Qed.  

Coercion sing (n : nat) := [n].

Lemma stack_discrete :
  discrete (stack bool).
Proof. 
  eapply discrete_iff; econstructor. intros ? ?. hnf. repeat decide equality.
Qed.

Lemma stack_enum :
  enumerable__T (stack bool).
Proof. (* This used to be solved by eauto. It is no longer. why?? *)
  unfold stack. eapply enumerator_enumerable, enumerator__T_to_list, enumerator__T_list, enumerator__T_of_list, enumerator__T_prod.
  all: eapply enumerator__T_to_list, enumerator__T_list.
  all: eapply enumerator__T_of_list, enumerator__T_bool.
Qed.

Local Definition BSRS := list (card bool).
Local Notation "x / y" := (x, y).
(* ** Enumerability *)

Fixpoint L_PCP n : list (BSRS * (string bool * string bool)) :=
  match n with
  | 0 => []
  | S n => L_PCP n
              ++ [ (C, (x, y)) | (C, x, y) ∈ (L_T BSRS n × L_T (string bool) n × L_T (string bool) n), (x/y) el C ]
              ++ [ (C, (x ++ u, y ++ v)) | ( (C, (u,v)), x, y) ∈ (L_PCP n × L_T (string bool) n × L_T (string bool) n), (x,y) el C ]
  end.

Lemma enum_PCP' :
  list_enumerator L_PCP (fun '(C, (u, v)) => @derivable bool C u v).
Proof.
  intros ( C & u & v ). split.
  + induction 1.
    * destruct (el_T C) as [m1], (el_T x) as [m2], (el_T y) as [m3].
      exists (1 + m1 + m2 + m3). cbn. in_app 2.
      in_collect (C, x, y); eapply cum_ge'; eauto; lia.
    * destruct IHderivable as [m1], (el_T x) as [m2], (el_T y) as [m3]. 
      exists (1 + m1 + m2 + m3). cbn. in_app 3.
      in_collect ( (C, (u, v), x, y)); eapply cum_ge'; eauto; try lia.
  + intros [m]. revert C u v H. induction m; intros.
    * inv H.
    * cbn in H. invert_list_in. 1: eauto. 1: econstructor; congruence. destruct p as (p1 & p2 & p3). destruct Dec; try congruence.
      injection H; intros <- <- <-. eapply der_cons; eauto.
Qed.

Lemma enumerable_derivable : enumerable (fun '(C, (u, v)) => @derivable bool C u v).
Proof.
  eapply list_enumerable_enumerable. eexists. eapply enum_PCP'.
Qed.

Lemma enumerable_PCP : enumerable dPCPb.
Proof.
  pose proof enumerable_derivable. 
  assert (enumerable (X := (stack bool * (string bool * string bool))) (fun '(C, (s, t)) => s = t)). {
    eapply dec_count_enum.
    - eapply decidable_iff. econstructor. intros (? & ? & ?). exact _.
    - eapply enum_enumT. econstructor. exact _.
  }
  unshelve epose proof (enumerable_conj _ _ _ _ H H0).
  - eapply discrete_iff. econstructor. exact _.
  - eapply projection in H1 as [f]. exists f.
    unfold enumerator in *.
    intros x. rewrite <- H1. intuition.
    + destruct H2 as [u]. exists (u,u). eauto.
    + destruct H2 as [[u v] [? ->]]. exists v. eauto.
Qed.



Section dec.

  Variable (X : Type) (eqX_dec : forall x y : X, { x = y } + { x <> y }).

  Fact is_a_head_dec (l t : list X) : { x : list X | l = t++x } + { ~ exists x : list X, l = t++x }.
  Proof using eqX_dec.
    revert t.
    induction l as [ | a l IHl ].
    + intros [ | t ]. 
      * left; exists nil; auto.
      * right; intros ([ | ] & ?); discriminate.
    + intros [ | b t ].
      * left; exists (a::l); auto.
      * destruct (eqX_dec a b) as [ -> | C ].
        - destruct (IHl t) as [ H | C ].
          ++ left; destruct H as (x & ->).
              exists x; auto.
          ++ right; contradict C; destruct C as (x & E).
             exists x; inversion E; subst; auto.
        - right; contradict C; destruct C as (? & E); inversion E; auto.
  Qed.
 
  Fact is_a_tail_dec (l t : list X) : { exists x : list X, x++t = l } + { ~ exists x : list X, x++t = l }.
  Proof using eqX_dec.
    destruct (is_a_head_dec (rev l) (rev t)) as [ H | H ].
    + left; destruct H as (x & Hx).
      exists (rev x).
      apply f_equal with (f := @rev _) in Hx.
      rewrite rev_app_distr in Hx.
      do 2 rewrite rev_involutive in Hx; auto.
    + right; contradict H.
      destruct H as (x & Hx); exists (rev x); subst.
      apply rev_app_distr.
  Qed.

End dec.

(* * The Post correspondence problem *)

Notation "R ⊳ s ∕ t" := (derivable R s t) (at level 70, format "R  ⊳  s ∕ t").

Section pcp_hand_dec.

  Variable (X : Type) (lc : list (list X * list X)).

  Notation pcp_hand := (fun s t => lc ⊳ s∕t).

  (* Any hand is either a card or of the for x++p/y++q where
      x/y is a non-void card and p/q is a hand *)

  Lemma pcp_hand_inv p q : 
           lc ⊳ p∕q -> In (p,q) lc 
                    \/ exists x y p' q', In (x,y) lc /\ lc ⊳ p'∕q' 
                                      /\ p = x++p' /\ q = y++q' 
                        /\  (x <> nil /\ y = nil  
                          \/ x = nil /\ y <> nil
                          \/ x <> nil /\ y <> nil ).
  Proof.
    induction 1 as [ x y H | x y p q H1 H2 IH2 ].
    + left; auto. 
    + destruct x as [ | a x ]; [ destruct y as [ | b y ] | ].
      * simpl; auto.
      * right; exists nil, (b::y), p, q; simpl; repeat split; auto.
        right; left; split; auto; discriminate.
      * right; exists (a::x), y, p, q; simpl; repeat split; auto.
        destruct y.
        - left; split; auto; discriminate.
        - right; right; split; discriminate.
  Qed.

  Section pcp_induction.

    Implicit Type (l m : list X).

    (* Notice that we could downgrade strict_suffix to Prop because
       a and b could be computed from the knowledge of their existence *)

    Definition strict_suffix x y l m := { a : _ & { b | (a <> nil \/ b <> nil) /\ l = a++x /\ m = b++y } }.
    
    Variable (P : list X -> list X -> Type)
             (IHP : forall l m, (forall l' m', strict_suffix l' m' l m -> P l' m') -> P l m).

    Theorem pcp_induction l m : P l m.
    Proof using IHP.
      induction on l m as IH with measure (length l + length m).
      apply IHP.
      intros l' m' (x & y & H & -> & ->).
      apply IH.
      do 2 rewrite length_app.
      destruct x; destruct y; simpl; try lia.
      destruct H as [ [] | [] ]; auto.
    Qed.

  End pcp_induction.

  (* ** PCP derivability is decidable *)
    
  Section bounded_dec.

    (* It is only possible to decide pcp_hand, when equality is decidable of course *)
  
    Variable eqX_dec : forall x y : X, { x = y } + { x <> y }.

    Let eqlX_dec : forall l m : list X, { l = m } + { l <> m }.
    Proof. apply list_eq_dec; auto. Qed.

    Let eqXX_dec : forall p q : list X * list X, { p = q } + { p <> q }.
    Proof. decide equality; auto. Qed.

    (* Replaced induction on length p + length q with strict suffix pair induction *)

    Theorem pcp_hand_dec p q : { lc ⊳ p∕q } + { ~ lc ⊳ p∕q }.
    Proof using eqlX_dec eqX_dec eqXX_dec.
      revert p q; apply pcp_induction; intros p q dec.

      set (P (c : list X * list X) := let (x,y) := c 
           in exists d, p = x++fst d /\ q = y++snd d /\ pcp_hand (fst d) (snd d) /\ (x <> nil \/ y <> nil)).
      assert (forall c, { P c } + { ~ P c }) as Pdec.
      { intros (x,y); simpl.
        assert ( { x = nil /\ y = nil } + { x <> nil \/ y <> nil } ) as H.
        1: { destruct (eqlX_dec x nil); destruct (eqlX_dec y nil); tauto. }
        destruct H as [ (H1 & H2) | Hxy ].
        1: { right; intros ((? & ?) & ?); tauto. }
        destruct (is_a_head_dec eqX_dec p x) as [ (p' & Hp') | Hp ].
        2: { right; contradict Hp; revert Hp. 
             intros ((p',?) & E & _); exists p'; auto. }
        destruct (is_a_head_dec eqX_dec q y) as [ (q' & Hq') | Hq ].
        2: { right; contradict Hq; revert Hq. 
             intros ((?,q') & _ & E & _); exists q'; auto. }
        destruct (dec p' q') as [ H' | H' ].
        + exists x, y; auto.
        + left; exists (p',q'); auto.
        + right; contradict H'; revert H'.
          intros ((u,v) & -> & -> & C & _); simpl in *.
          apply app_inv_head in Hp'.
          apply app_inv_head in Hq'.
          subst; auto. }

      destruct list_dec with (1 := Pdec) (l := lc)
        as [ ((x,y) & H1 & H) | H ]; unfold P in H.
      + left.
        destruct H as ((p',q') & -> & -> & H & _); simpl in *.
        constructor 2; auto.
      + destruct In_dec with (1 := eqXX_dec) (a := (p,q)) (l := lc)
          as [ H2 | H2 ].
        * left; constructor 1; auto.
        * right; contradict H2.
          apply pcp_hand_inv in H2.
          destruct H2 as [ | (x & y & p' & q' & H2 & H3 & -> & -> & H4) ]; auto.
          destruct H with (1 := H2).
          exists (p', q'); msplit 3; tauto.
    Qed.

  End bounded_dec.

End pcp_hand_dec.

