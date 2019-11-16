(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list utils_nat.

From Undecidability.Shared.Libs.DLW.Vec
  Require Import pos vec.

From Undecidability.Shared.Libs.DLW.Wf 
  Require Import acc_irr.

Set Implicit Arguments.

Section finite.

  Definition finite_t X := { lX | forall x : X, In x lX }.
  Definition finite X := exists lX, forall x : X, In x lX.

  Fact finite_t_finite X : finite_t X -> finite X.
  Proof. intros (l & ?); exists l; auto. Qed.

  Definition fin_t X (P : X -> Prop) := { l | forall x, P x <-> In x l }.
  Definition fin X (P : X -> Prop) := exists l, forall x, P x <-> In x l.

  Fact fin_t_fin X P : @fin_t X P -> fin P.
  Proof. intros (l & ?); exists l; auto. Qed.

  Fact finite_t_fin_t_eq X : (finite_t X -> fin_t (fun _ : X => True))
                           * (fin_t (fun _ : X => True) -> finite_t X).
  Proof.
    split; intros (l & ?); exists l; firstorder.
  Qed.

  Fact fin_t_map X Y (f : X -> Y) (P Q : _ -> Prop) : 
             (forall y, Q y <-> exists x, f x = y /\ P x)
          -> @fin_t X P
          -> @fin_t Y Q.
  Proof.
    intros H (lP & HP).
    exists (map f lP).
    intros x; rewrite in_map_iff, H.
    firstorder.
  Qed.

  Fact finite_t_map X Y (f : X -> Y) :
           (forall y, exists x, f x = y) 
        -> finite_t X 
        -> finite_t Y.
  Proof.
    intros H (l & Hl).
    exists (map f l).
    intros y.
    destruct (H y) as (x & <-).
    apply in_map_iff; exists x; auto.
  Qed.

  Fact Forall_reif_t X l (P : X -> Prop) : Forall P l -> { m : list (sig P) | map (@proj1_sig _ _) m = l }.
  Proof.
    induction l as [ | x l IHl ].
    + exists nil; auto.
    + intros H; rewrite Forall_cons_inv in H.
      destruct H as (H1 & H2).
      destruct (IHl H2) as (m & Hm).
      exists (exist _ x H1 :: m); simpl; f_equal; auto.
  Qed.

  Fact fin_t_finite_t X (P : X -> Prop) (Pirr : forall x (H1 H2 : P x), H1 = H2) :
         fin_t P -> finite_t (sig P).
  Proof.
    intros (l & Hl).
    destruct (@Forall_reif_t _ l P) as (m & Hm).
    + rewrite Forall_forall; intro; apply Hl.
    + exists m.
      intros (x & Hx).
      generalize Hx; intros H.
      rewrite Hl, <- Hm, in_map_iff in Hx.
      destruct Hx as (y & <- & Hy).
      eq goal Hy; f_equal.
      destruct y; simpl; f_equal; apply Pirr.
  Qed.

  Fact fin_t_equiv X (P Q : X -> Prop) : (forall x, P x <-> Q x) -> fin_t P -> fin_t Q.
  Proof.
    intros H (l & Hl); exists l.
    intro; rewrite <- H, Hl; tauto.
  Qed.

  Fixpoint list_prod X Y (l : list X) (m : list Y) :=
    match l with
      | nil  => nil
      | x::l => map (fun y => (x,y)) m ++ list_prod l m
    end.

  Fact list_prod_spec X Y l m c : In c (@list_prod X Y l m) <-> In (fst c) l /\ In (snd c) m.
  Proof.
    revert c; induction l as [ | x l IHl ]; intros c; simpl; try tauto.
    rewrite in_app_iff, IHl, in_map_iff; simpl.
    split.
    + intros [ (y & <- & ?) | (? & ?) ]; simpl; auto.
    + intros ([ -> | ] & ? ); destruct c; simpl; firstorder.
  Qed.

  Fact fin_t_prod X Y (P Q : _ -> Prop) : 
         @fin_t X P -> @fin_t Y Q -> fin_t (fun c => P (fst c) /\ Q (snd c)).
  Proof.
    intros (l & Hl) (m & Hm).
    exists (list_prod l m); intro; rewrite list_prod_spec, Hl, Hm; tauto.
  Qed.

  Fact finite_t_prod X Y : finite_t X -> finite_t Y -> finite_t (X*Y).
  Proof.
    intros (l & Hl) (m & Hm); exists (list_prod l m).
    intros []; apply list_prod_spec; auto.
  Qed.

  Fact finite_prod X Y : finite X -> finite Y -> finite (X*Y).
  Proof.
    intros (l & Hl) (m & Hm); exists (list_prod l m).
    intros []; apply list_prod_spec; auto.
  Qed.

  Fact fin_t_sum X Y (P Q : _ -> Prop) :
         @fin_t X P -> @fin_t Y Q -> fin_t (fun z : X + Y => match z with inl x => P x | inr y => Q y end).
  Proof.
    intros (l & Hl) (m & Hm).
    exists (map inl l ++ map inr m).
    intros z; rewrite in_app_iff, in_map_iff, in_map_iff.
    destruct z as [ x | y ]; [ rewrite Hl | rewrite Hm ].
    + split.
      * left; exists x; auto.
      * intros [ (z & E & ?) | (z & C & _) ]; try discriminate; inversion E; subst; auto.
    + split.
      * right; exists y; auto.
      * intros [ (z & C & _) | (z & E & ?) ]; try discriminate; inversion E; subst; auto.
  Qed.

  Fact finite_t_unit : finite_t unit.
  Proof. exists (tt::nil); intros []; simpl; auto. Qed.

  Fact finite_t_bool : finite_t bool.
  Proof. exists (true::false::nil); intros []; simpl; auto. Qed.

  Theorem fin_t_length X n : finite_t X -> fin_t (fun l => @length X l < n).
  Proof.
    intros HX.
    apply finite_t_fin_t_eq in HX.
    generalize finite_t_unit; intros H1.
    apply finite_t_fin_t_eq in H1.
    induction n as [ | n IHn ].
    + exists nil; intros; split; try lia; intros [].
    + generalize (fin_t_sum H1 (fin_t_prod HX IHn)).
      apply fin_t_map with (f := fun c => match c with
        | inl _     => nil
        | inr (x,l) => x::l
      end).
      intros [ | x l ]; simpl.
      * split; try lia; exists (inl tt); auto.
      * split.
        - intros Hl; exists (inr (x,l)); simpl; msplit 2; auto; lia.
        - intros ([ [] | (y,m) ] & E & H); try discriminate.
          simpl in *; inversion E; subst; lia.
  Qed.

  Theorem finite_t_list X n : finite_t X -> finite_t { l : list X | length l < n }.
  Proof.
    intros H; apply (fin_t_length n) in H; revert H; intros (l & Hl).
    assert (forall x, In x l -> length x < n) as f by (intro; apply Hl).
    set (g x Hx := exist (fun x => length x < n) x (f x Hx)).
    exists (list_in_map l g).
    intros (x & Hx).
    assert (G : In x l) by (revert Hx; apply Hl).
    assert (E : Hx = f _ G) by apply lt_pirr.
    subst Hx; apply In_list_in_map with (f := g).
  Qed.

  Theorem finite_t_option X : finite_t X -> finite_t (option X).
  Proof.
    intros (lX & HX).
    exists (None :: map Some lX).
    intros [x|]; simpl; auto.
    right; apply in_map_iff; exists x; auto.
  Qed.

  Fact finite_t_pos n : finite_t (pos n).
  Proof. exists (pos_list n); apply pos_list_prop. Qed.

  Theorem finite_t_vec X n : finite_t X -> finite_t (vec X n).
  Proof.
    intros HX.
    induction n as [ | n IHn ].
    + exists (vec_nil :: nil).
      intros v; vec nil v; simpl; auto.
    + apply finite_t_map with (f := fun c => vec_cons (fst c) (snd c)).
      * intros v; vec split v with x.
        exists (x,v); auto.
      * apply finite_t_prod; auto.
  Qed.

  Section dec.

    Variable (X : Type) (P : X -> Prop) (Pdec : forall x, { P x } + { ~ P x }).
    
    Theorem fin_t_dec Q : @fin_t X Q -> fin_t (fun x => P x /\ Q x).
    Proof.
      intros (l & Hl).
      exists (filter (fun x => if Pdec x then true else false) l).
      intros x; rewrite filter_In, <- Hl.
      destruct (Pdec x); try tauto.
      split; try tauto.
      intros []; discriminate.
    Qed.

  End dec.

  Fact finite_t_fin_t_dec (X : Type) (P : X -> Prop) (Pdec : forall x, { P x } + { ~ P x }) :
         finite_t X -> fin_t P.
  Proof. 
    intros H.
    apply finite_t_fin_t_eq in H.
    apply fin_t_dec with (1 := Pdec) in H.
    revert H; apply fin_t_equiv; tauto.
  Qed.

  Section list_reif.

    Variable (X Y : Type) (eqX_dec : forall x y : X, { x = y } + { x <> y })
             (R : X -> Y -> Prop).
    
    Theorem list_reif (l : list X) :
            (forall x, In x l -> exists y, R x y)
         -> exists f, forall x (Hx : In x l), R x (f x Hx).
    Proof.
      induction l as [ | x l IHl ]; intros Hl.
      + exists (fun x (Hx : @In X x nil) => False_rect Y Hx).
        intros _ [].
      + destruct (Hl x) as (y & Hy); simpl; auto.
        destruct IHl as (f & Hf).
        * intros; apply Hl; simpl; auto.
        * assert (forall z, In z (x::l) -> x <> z -> In z l) as H1.
          { intros z [ -> | ] ?; tauto. }
          exists (fun z Hz => 
            match eqX_dec x z with
              | left   _ => y
              | right  H => f z (H1 _ Hz H)
            end).
          intros z Hz.
          destruct (eqX_dec x z); subst; auto.
    Qed.

    Theorem list_reif_t (l : list X) :
            (forall x, In x l -> sig (R x))
         -> { f | forall x (Hx : In x l), R x (f x Hx) }.
    Proof.
      induction l as [ | x l IHl ]; intros Hl.
      + exists (fun x (Hx : @In X x nil) => False_rect Y Hx).
        intros _ [].
      + destruct (Hl x) as (y & Hy); simpl; auto.
        destruct IHl as (f & Hf).
        * intros; apply Hl; simpl; auto.
        * assert (forall z, In z (x::l) -> x <> z -> In z l) as H1.
          { intros z [ -> | ] ?; tauto. }
          exists (fun z Hz => 
            match eqX_dec x z with
              | left   _ => y
              | right  H => f z (H1 _ Hz H)
            end).
          intros z Hz.
          destruct (eqX_dec x z); subst; auto.
    Qed.  
 
  End list_reif.

  (** Will be useful to reify total relations into actual functions
      over finite and discrete domains *)

  Theorem finite_t_reif X Y (R : X -> Y -> Prop) : 
                              (forall x y : X, { x = y } + { x <> y })
                           -> finite_t X
                           -> (forall x : X, sig (R x))
                           -> { f | forall x, R x (f x) }.
  Proof.
    intros H1 (l & H2) H3.
    destruct list_reif_t with (1 := H1) (R := R) (l := l)
      as (f & Hf).
    + intros; auto.
    + exists (fun x => f x (H2 x)).
      intros; auto.
  Qed.

  Theorem finite_reif X Y R : (forall x y : X, { x = y } + { x <> y })
                           -> finite X
                           -> (forall x : X, exists y : Y, R x y)
                           -> exists f, forall x, R x (f x).
  Proof.
    intros H1 (l & H2) H3.
    destruct list_reif with (1 := H1) (R := R) (l := l)
      as (f & Hf).
    + intros; auto.
    + exists (fun x => f x (H2 x)).
      intros; auto.
  Qed.

End finite.

Theorem exists_dec_fin_t X (P Q : X -> Prop) 
           (Pdec : forall x, { P x } + { ~ P x }) 
           (HQ : fin_t Q)
           (HPQ : forall x, P x -> Q x) :
           { exists x, P x } + { ~ exists x, P x }.
Proof.
  generalize (fin_t_dec _ Pdec HQ); intros ([ | x l ] & Hl).
  + right; intros (x & Hx); apply (Hl x); split; auto.
  + left; exists x; apply Hl; simpl; auto.
Qed.

Definition bij_t (X Y : Type) := { i : X -> Y & { j | (forall x, j (i x) = x) /\ forall y, i (j y) = y } }.

Definition surj_t (X Y : Type) := { s : X -> Y | forall y, exists x, y = s x }.

Fact surj_t_compose X Y Z : surj_t X Y -> surj_t Y Z -> surj_t X Z.
Proof. 
  intros (f & Hf) (g & Hg); exists (fun x => g (f x)).
  intros z.
  destruct (Hg z) as (y & Hy).
  destruct (Hf y) as (x & Hx).
  exists x; subst; auto.
Qed.

Fact finite_t_surj_t X Y : surj_t X Y -> finite_t X -> finite_t Y.
Proof.
  intros [ s E ] (l & Hl).
  exists (map s l).
  intros y; rewrite in_map_iff. 
  destruct (E y) as (x & ?); exists x; auto. 
Qed.

Fact finite_t_pos_equiv X : (finite_t X -> { n : _ & surj_t (pos n) X })
                          * ({ n : _ & surj_t (pos n) X } -> finite_t X).
Proof.
  split.
  + intros (l & Hl).
    exists (length l).
    destruct (list_vec_full l) as (v & Hv).
    rewrite <- Hv in Hl.
    generalize (length l) v Hl.
    clear l v Hl Hv.
    intros n v H.
    exists (vec_pos v).
    intros x; apply (vec_list_inv _ _ (H x)).
  + intros (n & Hn).
    generalize (finite_t_pos n).
    apply finite_t_surj_t; auto.
Qed.

Fact NoDup_vec_list X n v : NoDup (@vec_list X n v) -> forall p q, vec_pos v p = vec_pos v q -> p = q.
Proof.
  induction v as [ | n x v IHv ]; intros H p q.
  + invert pos p.
  + simpl in H; rewrite NoDup_cons_iff in H.
    destruct H as [ H1 H2 ].
    invert pos p; invert pos q; intros E; auto.
    1,2: destruct H1; subst; apply in_vec_list, in_vec_pos.
    f_equal; apply IHv; auto.
Qed.

Fact finite_t_discrete_bij_t_pos X : 
        finite_t X
     -> (forall x y : X, { x = y } + { x <> y })
     -> { n : nat & bij_t X (pos n) }.
Proof. 
  intros (l' & Hl') D.
  generalize (NoDup_nodup D l') (nodup_In D l').
  set (l := nodup D l'); intros H1 H2.
  assert (Hl : forall x, In x l) by (intro; apply H2, Hl').
  revert H1 Hl.
  generalize l; clear l l' Hl' H2.
  intros l Hl1 Hl2.
  exists (length l).
  destruct (list_vec_full l) as (v & Hv).
  rewrite <- Hv in Hl1, Hl2.
  assert (forall x, in_vec x v) by (intro; apply in_vec_list; auto).
  generalize (NoDup_vec_list _ Hl1).
  clear Hl1 Hv.
  revert v H Hl2.
  generalize (length l); clear l.
  intros n v H1 H2 H3.
  destruct (finite_t_reif (fun x p => vec_pos v p = x) D) as 
    (f & Hf).
  + exists (vec_list v); auto.
  + intro; apply in_vec_dec_inv; auto.
  + exists f, (vec_pos v); split; auto.
Qed.







