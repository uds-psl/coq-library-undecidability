(* * Trakhtenbrot's Theorem *)
Require Import Lia Arith.

Require Import Undecidability.PCP.PCP.
Require Import Undecidability.PCP.Util.PCP_facts.
Require Import Undecidability.Synthetic.DecidabilityFacts.
From Undecidability Require Import FOL.Utils.FullSyntax.
From Undecidability Require FOL.Semantics.FiniteTarski.Fragment.
From Undecidability Require Import FOL.FSAT.
Require Import Undecidability.Shared.ListAutomation.
Import ListAutomationNotations.

Set Default Proof Using "Type".
Local Unset Strict Implicit.

(* ** Bounded boolean strings *)

Local Notation "| s |" := (length s) (at level 100).

Definition bstring n :=
  { s : string bool | | s | <= n}.

Lemma string_nil (s : string bool) :
  |s| <= 0 <-> s = nil.
Proof.
  destruct s; cbn.
  - split; trivial; lia.
  - split; try congruence. intros H. lia.
Qed.

Definition bnil n : bstring n := exist _ nil (Nat.le_0_l n).

Definition bcons n (b : bool) (H : bstring n) : bstring (S n) :=
  match H with 
    exist _ bs Hs => exist _ (b::bs) (le_n_S (|bs|) n Hs) end.

Lemma bstring_eq n (s t : bstring n) :
  proj1_sig s = proj1_sig t <-> s = t.
Proof.
  split; try now intros ->.
  destruct s as [s H1], t as [t H2]; cbn.
  intros ->. now rewrite (le_unique _ _ H1 H2).
Qed.

Lemma bstring_eq' n (s t : bstring n) :
  proj1_sig s = proj1_sig t -> s = t.
Proof.
  apply bstring_eq.
Qed.

Definition bstring_step n (L : list (bstring n)) :=
  [bnil (S n)] ++ map (bcons true) L ++ map (bcons false) L.

Definition bcast n s (H : |s| <= n) : bstring n :=
  exist _ s H.

Lemma listable_bstring n :
  listable (bstring n).
Proof.
  induction n.
  - exists [bnil 0]. intros [s H].
    assert (s = nil) as -> by now apply string_nil.
    left. now apply bstring_eq.
  - destruct IHn as [L HL]. exists (bstring_step L).
    intros [ [|[] s] H]; apply in_app_iff; cbn in H.
    + left. left. now apply bstring_eq.
    + right. apply in_app_iff. left. apply in_map_iff.
      assert (H' : |s| <= n) by lia. exists (bcast H').
      split; trivial. now apply bstring_eq.
    + right. apply in_app_iff. right. apply in_map_iff.
      assert (H' : |s| <= n) by lia. exists (bcast H').
      split; trivial. now apply bstring_eq.
Qed.


Notation i_f b x := (@i_func _ _ _ _ (f b) (Vector.cons _ x _ (Vector.nil _))).
Definition i_f' {domain:Type} {i:interp domain} (b:bool) (x:domain) := i_f b x.

Notation i_e := (@i_func _ _ _ _ e (Vector.nil _)).

Notation i_dum := (@i_func _ _ _ _ dum (Vector.nil _)).

Notation i_P x y := (@i_atom _ _ _ _ P (Vector.cons _ x _ (Vector.cons _ y _ (Vector.nil _)))).

Notation i_less x y := (@i_atom _ _ _ _ less (Vector.cons _ x _ (Vector.cons _ y _ (Vector.nil _)))).

Notation i_equiv x y := (@i_atom _ _ _ _ equiv (Vector.cons _ x _ (Vector.cons _ y _ (Vector.nil _)))).

Fixpoint iprep domain {I : interp domain} (x : list bool) (y : domain) :=
  match x with
  | nil => y
  | b::x => i_f b (iprep x y)
  end.

Definition ienc domain {I : interp domain} (x : list bool) := iprep x i_e.


Local Definition BSRS := list (card bool).
Local Notation "x / y" := (x, y).

(* ** Finite standard models *)

Section FIB.

  Variable R : BSRS.

  Definition obstring n :=
    option (bstring n).

  Lemma listable_obstring n :
    listable (obstring n).
  Proof.
    destruct (listable_bstring n) as [L HL]. exists (None :: map Some L).
    intros [x|].
    - right. apply in_map, HL.
    - cbn. eauto.
  Qed.

  Notation obcast H := (Some (bcast H)).

  Definition ccons n b (s : obstring n) : obstring n :=
  match s with
  | Some (exist _ s _) => match (le_dec (|b::s|) n) with
             | left H => obcast H
             | right _ => None
             end
  | None => None
  end.

  Definition cdrv n (s t : obstring n) :=
    match s, t with
      | Some (exist _ s _), Some (exist _ t _) => derivable R s t
      | _, _ => False
    end.

  Definition sub n (x y : obstring n) :=
    match x, y with
    | Some (exist _ s _), Some (exist _ t _) => s <> t /\ exists s', t = s'++s 
    | _, _ => False
    end.
  
  Global Instance FIB n : interp (obstring n).
  Proof using R.
    split.
    - intros k; cbn. destruct k as [b | |].
      + intros v. exact (ccons b (Vector.hd v)).
      + intros _. exact (Some (bnil n)).
      + intros _. exact None.
    - intros k; cbn. destruct k.
      + intros v. exact (cdrv (Vector.hd v) (Vector.hd (Vector.tl v))).
      + intros v. exact (sub (Vector.hd v) (Vector.hd (Vector.tl v))).
      + intros v. exact (eq (Vector.hd v) (Vector.hd (Vector.tl v))).
  Defined.
  

  (* The PCP instance R is solvable iff a solution is derivable in a finite standard model. *)

  Lemma app_bound n (s t : string bool) :
    |t| <= n -> |s++t| <= n + |s|.
  Proof.
    intros H. rewrite app_length. lia.
  Qed.

  Lemma obstring_iprep n x u (HX : |x++u| <= n) (HU : |u| <= n) :
    iprep x (obcast HU) = obcast HX.
  Proof.
    induction x; cbn.
    - f_equal. now apply bstring_eq.
    - assert (H : |x++u| <= n).
      { rewrite app_length in *. cbn in HX. lia. }
      rewrite (IHx H). unfold ccons, bcast at 1. destruct le_dec.
      + f_equal. now apply bstring_eq.
      + exfalso. cbn in *. rewrite app_length in *. lia.
  Qed.

  Lemma obstring_ienc n s (H : |s| <= n) :
    ienc s = obcast H.
  Proof.
    unfold ienc. cbn.
    setoid_rewrite obstring_iprep. 
    f_equal. apply bstring_eq, app_nil_r.
    Unshelve. rewrite app_length. cbn. lia.
  Qed.

  Lemma obstring_ienc' n s (H : ~ |s| <= n) :
    @ienc _ (FIB n) s = None.
  Proof.
    induction s; cbn in *; try lia.
    change (@ccons n a (ienc s) = None).
    destruct (le_dec (|s|) n) as [H'|H'].
    - setoid_rewrite (obstring_ienc H'). cbn.
      destruct le_dec; tauto.
    - now rewrite IHs.
  Qed.

  Lemma crdv_iff n (x y : obstring n) :
    i_P x y <-> exists s t, derivable R s t /\ x = ienc s /\ y = ienc t /\ |s| <= n /\ |t| <= n.
  Proof.
    destruct x as [ [x HX]|], y as [ [y HY]|]; split; cbn; auto.
    { intros H. exists x, y. repeat setoid_rewrite obstring_ienc. now repeat split. }
    all: intros (s&t&H1&H2&H3&H4&H5). all: try unshelve setoid_rewrite obstring_ienc in H2; try unshelve setoid_rewrite obstring_ienc in H3; auto.
    all: try discriminate.
    revert H2 H3. now intros [= ->] [= ->].
  Qed.

  Definition obembed n (s : obstring n) : obstring (S n) :=
    match s with
    | Some (exist _ s H) => Some (exist _ s (le_S _ _ H))
    | None => None
    end.

  Lemma cdrv_mon n (s t : obstring n) :
    cdrv s t -> @cdrv (S n) (obembed s) (obembed t).
  Proof.
    now destruct s as [ [s HS]|], t as [ [t HT]|].
  Qed.

  Lemma cdrv_mon' n s t :
    @cdrv n (ienc s) (ienc t) -> @cdrv (S n) (ienc s) (ienc t).
  Proof.
    destruct (le_dec (|s|) n) as [H|H], (le_dec (|t|) n) as [H'|H'].
    - repeat unshelve setoid_rewrite obstring_ienc; trivial; lia.
    - setoid_rewrite (obstring_ienc H). setoid_rewrite (obstring_ienc' H'). cbn. tauto.
    - rewrite (obstring_ienc' H). cbn. tauto.
    - rewrite (obstring_ienc' H). cbn. tauto.
  Qed.

  Lemma drv_cdrv s t :
    derivable R s t <-> @cdrv (max (|s|) (|t|)) (ienc s) (ienc t).
  Proof.
    repeat unshelve setoid_rewrite obstring_ienc; try reflexivity; lia.
  Qed.

  Lemma drv_cdrv' s :
    derivable R s s <-> @cdrv (|s|) (ienc s) (ienc s).
  Proof.
   repeat unshelve setoid_rewrite obstring_ienc; try reflexivity; lia.
  Qed.

  Lemma BPCP_P :
    dPCPb R <-> exists n x, @i_atom _ _ _ (FIB n) P ((Vector.cons _ x _ (Vector.cons _ x _ (Vector.nil _)))).
  Proof.
    split.
    - intros [s H]. exists (|s|), (ienc s). cbn. now apply drv_cdrv'.
    - intros [n[ [ [s H]|] H'] ].
      + cbn in H'. now exists s.
      + destruct H'.
  Qed.

  (* FIB satisfies the axioms used later. *)

  Section Ax.
    
    Variable n : nat.
    Implicit Type x y : obstring n.

    Lemma app_eq_nil' (s t : string bool) :
      s = t++s -> t = nil.
    Proof.
      destruct t; trivial. intros H. exfalso.
      assert (H' : |s| = |(b :: t) ++ s|) by now rewrite H at 1.
      cbn in H'. rewrite app_length in H'. lia.
    Qed.

    Lemma app_neq b (s t : string bool) :
      s <> (b :: t) ++ s.
    Proof.
      intros H. apply app_eq_nil' in H. discriminate.
    Qed.

    Lemma FIB_HP x y :
      i_P x y -> x <> None /\ y <> None.
    Proof.
      destruct x as [ [s HS] |], y as [ [t HT]|]; auto.
      intros _. split; discriminate.
    Qed.

    Lemma FIB_HS1 x :
      ~ sub x x.
    Proof.
      destruct x as [ [s HS]|]; cbn; firstorder.
    Qed.

    Lemma FIB_HS2 x y z :
      sub x y -> sub y z -> sub x z.
    Proof.
      destruct x as [ [s HS]|], y as [ [t HT]|], z as [ [u HU]|]; cbn; auto.
      intros [H1[s' HS'] ] [H2[t' HT'] ]. subst. split.
      - rewrite app_assoc. intros H % app_eq_nil'.
        apply app_eq_nil in H as [-> ->]. now apply H1.
      - exists (t'++s'). apply app_assoc.
    Qed.
      
    Lemma FIB_HF1 b x :
      i_f b x <> i_e.
    Proof.
      destruct x as [ [s H]|]; cbn; try congruence.
      destruct le_dec; try congruence. injection. congruence.
    Qed.

    Lemma FIB_HF2 b1 b2 x y : 
      i_f b1 x <> None -> i_f b1 x = i_f b2 y -> x = y /\ b1 = b2.
    Proof.
      destruct x as [ [s HS] |], y as [ [t HT]|]; cbn.
      all: repeat destruct le_dec; cbn. all: try congruence.
      intros _ [= -> ->]. split; trivial. f_equal. now apply bstring_eq.
    Qed.

    Lemma None_dec X (x : option X) :
      {x = None} + {x <> None}.
    Proof.
      destruct x; auto. right. discriminate.
    Qed.

    Lemma FIB_HF2'  x y : 
      i_f true x = i_f false y -> i_f true x = None /\ i_f false y = None.
    Proof.
      intros H. destruct (None_dec (i_f' true x)), (None_dec (i_f' false y)); try tauto; exfalso. all: unfold i_f'.
      - symmetry in H. specialize (FIB_HF2 n0 H). intros [H1 H2]; congruence.
      - specialize (FIB_HF2 n0 H). intros [H1 H2]; congruence.
      - specialize (FIB_HF2 n0 H). intros [_ H']. discriminate.
    Qed.
    
    Lemma FIB_HF3 b x :
      i_f b x <> None -> x <> None.
    Proof.
      destruct x as [ [s HS] |]; cbn; congruence.
    Qed.

    Lemma FIB_HI x y :
      i_P x y -> (exists s t, s/t el R /\ x = ienc s /\ y = ienc t)
                \/ (exists s t u v, s/t el R /\ x = iprep s u /\ y = iprep t v /\ i_P u v /\
                              ((sub u x /\ v = y) \/ (sub v y /\ u = x) \/ (sub u x /\ sub v y))).
    Proof.
      destruct x as [ [x HX]|], y as [ [y HY]|]; cbn; auto. induction 1.
      - left. exists x, y. repeat setoid_rewrite obstring_ienc. repeat split; trivial.
      - assert (HU : |u| <= n). { rewrite app_length in HX. lia. }
        assert (HV : |v| <= n). { rewrite app_length in HY. lia. }
        destruct x as [|b x], y as [|c y].
        + cbn. apply IHderivable.
        + right. exists [], (c::y), (obcast HU), (obcast HV).
          repeat setoid_rewrite obstring_iprep. repeat split; trivial.
          right. left. repeat split; eauto using app_neq. f_equal. now apply bstring_eq.
        + right. exists (b::x), [], (obcast HU), (obcast HV).
          repeat setoid_rewrite obstring_iprep. repeat split; trivial.
          left. repeat split; eauto using app_neq. f_equal. now apply bstring_eq.
        + right. exists (b::x), (c::y), (obcast HU), (obcast HV).
          repeat setoid_rewrite obstring_iprep. repeat split; trivial.
          right. right. repeat split; eauto using app_neq.
    Qed.

  End Ax.

End FIB.




(* ** Axiomatisation of finite standard models *)

Section Conv.
  
  Variable R : BSRS.
  
  Variable D : Type. 
  Hypothesis HD : listable D.

  Variable I : interp D.

  Notation "x == y" := (i_equiv x y) (at level 50).
  Notation "x =/= y" := (~ (i_equiv x y)) (at level 50).

  Hypothesis HP : forall x y, i_P x y -> x =/= i_dum /\ y =/= i_dum.

  Hypothesis HS1 : forall x, ~ i_less x x.
  Hypothesis HS2 : forall x y z, i_less x y -> i_less y z -> i_less x z.

  Hypothesis HF1 : forall b x, i_f b x =/= i_e.
  Hypothesis HF2 : forall b1 b2 x y, i_f b1 x =/= i_dum -> i_f b1 x == i_f b2 y -> x == y /\ b1 = b2.
  Hypothesis HF3 : forall b x, i_f b x =/= i_dum -> x =/= i_dum.

  Hypothesis HE1 : forall x, x == x.
  Hypothesis HE2 : forall x y, x == y -> y == x.
  Hypothesis HE3 : forall x y z, x == y -> y == z -> x == z.
  Hypothesis HER1 : forall x y b, x == y -> i_f b x == i_f b y.
  Hypothesis HER3 : forall x1 x2 y1 y2, x1 == x2 -> y1 == y2 -> i_less x1 y1 -> i_less x2 y2.

  Hypothesis HI :
    forall x y, i_P x y -> (exists s t, s/t el R /\ x == ienc s /\ y == ienc t)
                     \/ (exists s t u v, s/t el R /\ x == iprep s u /\ y == iprep t v /\ i_P u v /\
                                   ((i_less u x /\ v == y) \/ (i_less v y /\ u == x) \/ (i_less u x /\ i_less v y))).

  (* Any solution of R that holds in a model satisfying the axioms gives rise to an actual solution. *)
      
  Lemma ienc_inj s t :
    ienc s =/= i_dum -> ienc s == ienc t -> s = t.
  Proof using HF3 HF2 HF1 HE2.
    revert t. induction s; intros [|]; cbn; trivial.
    - intros _ H. apply HE2 in H. now apply HF1 in H.
    - intros _ H. now apply HF1 in H.
    - intros H [H' ->] % HF2; trivial. f_equal.
      apply IHs; trivial. apply HF3 in H. trivial.
  Qed.

  Definition sub' L x y :=
    i_less x y /\ x el L.
  
  Lemma sub_acc_pred L x y :
    i_less y x -> Acc (sub' L) x -> Acc (sub' L) y.
  Proof using HS2.
    intros H H'. constructor. intros z [H1 H2].
    apply H'. split; trivial. now apply (HS2 H1).
  Qed.

  Lemma sub_acc_cons L x y :
    Acc (sub' L) x -> ~ i_less y x -> Acc (sub' (y::L)) x.
  Proof using HS2 HD.
    induction 1 as [x HX IH]. intros H.
    constructor. intros z [H1[->|H2] ].
    - contradiction.
    - apply IH. 1: now split.
      intros HH. now eapply H, HS2 with z.
  Qed.

  Lemma sub_acc_cons' L x y :
    i_less y x -> Acc (sub' L) x -> Acc (sub' (y::L)) y.
  Proof using HS2 HS1 HD.
    intros H1 H2. apply sub_acc_cons; trivial.
    now apply (sub_acc_pred H1).
  Qed.

  Lemma sub_acc_step L a x :
    Acc (sub' L) x -> Acc (sub' (a::L)) x.
  Proof using HS2 HS1 HD.
    induction 1 as [x HX IH].
    constructor. intros y [H [->|H'] ].
    - now apply (sub_acc_cons' H).
    - apply IH. now split.
  Qed.

  Lemma sub_acc' L x :
    Acc (sub' L) x.
  Proof using HS2 HS1 HD.
    induction L.
    - constructor. intros y [_ [] ].
    - apply sub_acc_step, IHL.
  Qed.

  Lemma sub_acc x :
    Acc (fun a b => i_less a b) x.
  Proof using HS2 HS1 HD.
    destruct HD as [L HL].
    induction (sub_acc' L x) as [x _ IH].
    constructor. intros y H. now apply IH.
  Qed.

  Inductive psub : D -> D -> D -> D -> Prop :=
  | psub1 x u y y' : i_less u x -> y == y' -> psub u y x y'
  | psub2 y u x x' : i_less u y -> x == x' -> psub x u x' y
  | psub3 x y u v : i_less u x -> i_less v y -> psub u v x y.

  Lemma psub_equiv a b c d a' b' c' d' :
    a == a' -> b == b' -> c == c' -> d == d' ->
    psub a b c d -> psub a' b' c' d'.
  Proof using HE2 HE3 HER3.
    intros Ha Hb Hc Hd Habcd. induction Habcd as [c a b d Hac Hbd|d b a c Hdb Hac|c d a b Hac Hdb] in Ha,Hb,Hc,Hd,a',b',c',d'|-*.
    + eapply psub1.
      - now eapply HER3 with a c.
      - eapply HE3 with b. 1: now eapply HE2.
        now eapply HE3 with d.
    + eapply psub2.
      - now eapply HER3 with b d.
      - eapply HE3 with a. 1: now eapply HE2.
        now eapply HE3 with c.
    + eapply psub3.
      - now eapply HER3 with a c.
      - now eapply HER3 with b d.
  Qed.

  Definition psub' : D * D -> D * D -> Prop := fun P1 P2 => let (a,b) := P1 in let (c,d) := P2 in psub a b c d.

  Definition pequiv : D * D -> D * D -> Prop := fun P1 P2 => let (a,b) := P1 in let (c,d) := P2 in a == c /\ b == d.

  Lemma pequiv_equiv : RelationClasses.Equivalence pequiv.
  Proof using HE1 HE2 HE3.
    split.
    - intros [x y]. split; now apply HE1.
    - intros [x1 y1] [x2 y2] [H1 H2]; split; now apply HE2.
    - intros [x1 y1] [x2 y2] [x3 y3] [Hx1 Hx2] [Hy1 Hy2]; split; [eapply HE3 with x2 | eapply HE3 with y2]; easy.
  Qed.

  Lemma psub_acc p :
    Acc psub' p.
  Proof using HS2 HS1 HD HI HE1 HE2 HE3 HER3.
    destruct p as [x y]. revert y.
    induction (sub_acc x) as [x HX IHX]. intros y.
    induction (sub_acc y) as [y HY IHY]. constructor.
    intros [u v]. cbn. inversion 1; subst.
    - now apply IHX.
    - eapply (Morphisms_Prop.Acc_pt_morphism pequiv) with (x, v).
      + apply pequiv_equiv.
      + intros [a b] [a' b'] [Ha Hb] [c d] [c' d'] [Hc Hd]. split; apply psub_equiv; (try easy); apply HE2; easy.
      + now split.
      + apply IHY. easy.
    - now apply IHX.
  Qed.

  Lemma ienc_iprep s t :
    iprep s (ienc t) == ienc (s ++ t).
  Proof using HER1 HE3 HE1.
    induction s; cbn; trivial. apply HER1. apply (HE3 IHs). apply HE1.
  Qed.

  Lemma iprep_respectful s t t' : t == t' -> iprep s t == iprep s t'.
  Proof using HER1.
  intros Ht. induction s.
  - cbn. easy.
  - cbn. apply HER1. easy.
  Qed.

  Lemma P_drv' p :
    i_P (fst p) (snd p) -> exists s t, derivable R s t /\ fst p == ienc s /\ snd p == ienc t.
  Proof using HS2 HS1 HI HD HE1 HE2 HE3 HER1 HER3.
    intros H. induction (psub_acc p) as [ [x' y'] _ IH]; cbn in *.
    destruct (HI H) as [(s&t&H1&H2&H3)|(s&t&u&v&H1&H2&H3&H4&H5)]; subst.
    - exists s, t. repeat split; trivial. now constructor.
    - destruct (IH (u,v)) as (s'&t'&H6&H7&H'); cbn in *; trivial; subst.
      + destruct H5 as [ [H5 H5r]|[ [H5 H5r]|[] ] ].
        * now apply psub1.
        * now apply psub2.
        * now apply psub3.
      + exists (s++s'), (t++t'). repeat split. 1: now right.
        * apply (HE3 H2). eapply HE3. 2: apply ienc_iprep. apply iprep_respectful. easy.
        * apply (HE3 H3). eapply HE3. 2: apply ienc_iprep. apply iprep_respectful. easy. 
  Qed.

  Lemma P_drv x y :
    i_P x y -> exists s t, derivable R s t /\ x == ienc s /\ y == ienc t.
  Proof using HS2 HS1 HI HD HE1 HE2 HE3 HER1 HER3.
    apply P_drv' with (p:=(x,y)).
  Qed.

  Lemma P_BPCP x :
    i_P x x -> dPCPb R.
  Proof using HS2 HS1 HP HI HF3 HF2 HF1 HD HE1 HE2 HE3 HER1 HER3.
    intros H. destruct (P_drv H) as (s&t&H1&H2&H3); subst.
    assert (ienc s == ienc t) as H4.
    - apply HE3 with x. now apply HE2. easy.
    - apply ienc_inj in H4. exists t. congruence. destruct (@HP x x) as [Hx _]. 1:easy.
      intros Hcc. apply Hx. now apply HE3 with (ienc s).
  Qed.

End Conv.



(* ** Axioms stated as a concrete first-order formula *)

Section Reduction.
Notation t_f b x := (func (f b) (Vector.cons _ x _ (Vector.nil _))).

Notation t_e :=
  (func e (Vector.nil _)).

Notation t_dum :=
  (func dum (Vector.nil _)).

Notation f_P x y := (atom P (Vector.cons _ x _ (Vector.cons _ y _ (Vector.nil _)))).

Notation f_less x y := (atom less (Vector.cons _ x _ (Vector.cons _ y _ (Vector.nil _)))).

Notation f_equiv x y := (atom equiv (Vector.cons _ x _ (Vector.cons _ y _ (Vector.nil _)))).

  Notation "x ≡ y" := (f_equiv x y) (at level 20).
  Notation "x ≢ y" := (¬ (x ≡ y)) (at level 20).
  Notation "x ≺ y" := (f_less x y) (at level 20).

  Fixpoint tprep (x : list bool) (y : term) :=
    match x with
    | nil => y
    | b::x => t_f b (tprep x y)
    end.

  Lemma tprep_eval D (I : interp D) rho x t :
    eval rho (tprep x t) = iprep x (eval rho t).
  Proof.
    induction x; cbn.
    - reflexivity.
    - rewrite IHx. reflexivity.
  Qed.

  Lemma tprep_bounded x t n : bounded_t n t -> bounded_t n (tprep x t).
  Proof.
    intros H; induction x; solve_bounds. 1: apply H.
    apply IHx.
  Qed.

  Definition tenc (x : list bool) := tprep x t_e.

  Definition ax_P := ∀ ∀ f_P $1 $0 → ($1 ≢ t_dum) ∧ ($0 ≢ t_dum).
  Definition ax_S1 := ∀ ¬ ($0 ≺ $0).
  Definition ax_S2 := ∀ ∀ ∀ $2 ≺ $1 → $1 ≺ $0 → $2 ≺ $0.

  Definition ax_HF1_true := ∀ t_f true $0 ≢ t_e.
  Definition ax_HF1_false := ∀ t_f false $0 ≢ t_e.
  Definition ax_HF2_true := ∀ ∀ t_f true $1 ≢ t_dum → t_f true $1 ≡ t_f true $0 → $1 ≡ $0.
  Definition ax_HF2_false := ∀ ∀ t_f false $1 ≢ t_dum → t_f false $1 ≡ t_f false $0 → $1 ≡ $0.
  Definition ax_HF2 := ∀ ∀ t_f true $1 ≡ t_f false $0 → (t_f true $1 ≡ t_dum ∧ t_f false $0 ≡ t_dum).

  Definition ax_HF3_true := ∀ t_f true $0 ≢ t_dum → $0 ≢ t_dum.
  Definition ax_HF3_false := ∀ t_f false $0 ≢ t_dum → $0 ≢ t_dum.

  Definition ax_HE1 := ∀ $0 ≡ $0.
  Definition ax_HE2 := ∀ ∀ $1 ≡ $0 → $0 ≡ $1.
  Definition ax_HE3 := ∀ ∀ ∀ $2 ≡ $1 → $1 ≡ $0 → $2 ≡ $0.

  Definition ax_HER1_true := ∀ ∀ $1 ≡ $0 → t_f true $1 ≡ t_f true $0.
  Definition ax_HER1_false := ∀ ∀ $1 ≡ $0 → t_f false $1 ≡ t_f false $0.
  Definition ax_HER3 := ∀ ∀ ∀ ∀ $3 ≡ $2 → $1 ≡ $0 → f_less $3 $1 → f_less $2 $0.

  Definition ax_HI' c :=
    ($1 ≡ tenc (fst c) ∧ $0 ≡ tenc (snd c))
    ∨ (∃ ∃ $3 ≡ tprep (fst c) $1 ∧ $2 ≡ tprep (snd c) $0 ∧ f_P $1 $0
           ∧ (($1 ≺ $3 ∧ $0 ≡ $2) ∨ ($0 ≺ $2 ∧ $1 ≡ $3) ∨ ($1 ≺ $3 ∧ $0 ≺ $2))).

  Fixpoint list_or (A : list form) : form :=
    match A with 
    | nil => ⊥
    | phi::A => phi ∨ list_or A
    end.

  Lemma list_or_spec A D (I : interp D) rho :
    rho ⊨ list_or A <-> exists phi, phi el A /\ rho ⊨ phi.
  Proof.
    induction A; cbn; split; auto.
    - firstorder.
    - intros [H|H].
      + exists a. tauto.
      + apply IHA in H as [phi[H1 H2]]. exists phi. tauto.
    - intros [phi [[->|H1] H]]; auto.
      right. apply IHA. now exists phi.
  Qed.

  Lemma list_or_closed n A : (forall a, In a A -> bounded n a) -> bounded n (list_or A).
  Proof.
    intros H. induction A; solve_bounds.
    - apply H. now left.
    - apply IHA. intros a' Ha. apply H. now right.
  Qed.

  Definition ax_HI (R : BSRS) := ∀ ∀ f_P $1 $0 → list_or (map ax_HI' R).

  Definition finsat_formula (R : BSRS) :=
    ax_P ∧ ax_S1 ∧ ax_S2 ∧ ax_HF1_true ∧ ax_HF1_false ∧ ax_HF2_true ∧ ax_HF2_false
    ∧ ax_HF2 ∧ ax_HF3_true ∧ ax_HF3_false ∧ ax_HI R 
    ∧ ax_HE1 ∧ ax_HE2 ∧ ax_HE3 ∧ ax_HER1_true ∧ ax_HER1_false ∧ ax_HER3
    ∧ ∃ f_P $0 $0.

  Lemma finsat_closed R : closed (finsat_formula R).
  Proof.
    unfold closed. solve_bounds.
    apply list_or_closed.
    intros a [x [<- Hx2]]%in_map_iff.
    solve_bounds. all: apply tprep_bounded; solve_bounds.
  Qed.

  (* Verification of the reduction *)
  Ltac rsplit n := let rec f n := match n with 0 => idtac | S ?nn => split; [f nn|idtac] end in f n.

  Lemma obstring_eqdec n : eq_dec (obstring n).
  Proof.
    apply option_eq_dec. unfold bstring.
    intros [a Ha] [b Hb]. destruct (list_eq_dec bool_eq_dec a b) as [Hn0|Hn0].
    - subst. left. apply EqdepFacts.eq_dep_eq_sig. assert (Ha = Hb) as -> by (apply le_unique). constructor.
    - right. intros H. eapply Hn0, EqdepFacts.eq_sig_fst. exact H.
  Defined.

  Definition cdrv_decider (R : BSRS) (n : nat) (s t : obstring n) : dec (cdrv R s t).
  Proof.
    destruct s as [[s Hs]|], t as [[t Ht]|].
    - cbn. apply pcp_hand_dec. apply bool_eq_dec.
    - cbn. now right.
    - cbn. now right.
    - cbn. now right.
  Defined.
  Definition sub_decider (n : nat) (s t : obstring n) : dec (sub s t).
  Proof.
    destruct s as [[s Hs]|], t as [[t Ht]|].
    - cbn. destruct (list_eq_dec bool_eq_dec s t) as [Hl|Hr].
      + right. intros [H _]. tauto.
      + destruct (is_a_tail_dec bool_eq_dec t s) as [Hl2|Hr2].
        * left. split; try easy. destruct Hl2 as [x Hx]. exists x. congruence.
        * right. intros [_ [x Hx]]. apply Hr2. exists x. congruence. 
    - cbn. now right.
    - cbn. now right.
    - cbn. now right.
  Defined.

  Lemma signature_is_decidable n R : (forall p : syms_pred, decidable (fun v : Vector.t (obstring n) (ar_preds p) => @i_atom _ _ (obstring n) (@FIB R n) p v)).
  Proof.
    intros [| |]; cbn.
    - exists (fun X => if cdrv_decider R (Vector.hd X) (Vector.hd (Vector.tl X)) then true else false).
      intros X. destruct (cdrv_decider R (Vector.hd X) (Vector.hd (Vector.tl X))) as [Ht|Hf]; now split.
    - exists (fun X => if sub_decider (Vector.hd X) (Vector.hd (Vector.tl X)) then true else false).
      intros X. destruct (sub_decider (Vector.hd X) (Vector.hd (Vector.tl X))) as [Ht|Hf]; now split.
    - exists (fun X => if obstring_eqdec (Vector.hd X) (Vector.hd (Vector.tl X)) then true else false).
      intros X. destruct (obstring_eqdec (Vector.hd X) (Vector.hd (Vector.tl X))) as [Ht|Hf]; now split.
  Qed.

  Theorem finsat_reduction_1 R :
    dPCPb R -> FSATd (finsat_formula R).
  Proof.
    intros H.
    - apply BPCP_P in H as [n [s H]]. exists (obstring n), (@FIB R n), (fun _ => None).
      split; try apply listable_obstring. cbn.
      split. 2:split. 2: apply signature_is_decidable.
      1: {exists (fun '(a,b) => if obstring_eqdec a b then true else false).
          intros [a b]. destruct (obstring_eqdec a b) as [Ht|Hf]; now split. }
      rsplit 17.
      + apply (@FIB_HP R).
      + apply FIB_HS1.
      + apply FIB_HS2.
      + intros x. apply (@FIB_HF1 R _ true x).
      + intros x. apply (@FIB_HF1 R _ false x).
      + intros x y H1 H2. now destruct (FIB_HF2 (R:=R) H1 H2).
      + intros x y H1 H2. now destruct (FIB_HF2 (R:=R) H1 H2).
      + apply (@FIB_HF2' R).
      + intros x. apply (@FIB_HF3 R _ true x).
      + intros x. apply (@FIB_HF3 R _ false x).
      + intros u v [[a[b[H1 H2]]]|[a[b[a'[b'[H1 H2]]]]]] % (@FIB_HI R _ u v); apply list_or_spec.
      * exists (ax_HI' (a/b)). split; try now apply in_map.
        left. cbn. now rewrite !tprep_eval.
      * exists (ax_HI' (a/b)). split; try now apply in_map.
        right. exists a', b'. cbn. rewrite !tprep_eval. tauto.
      + congruence.
      + congruence.
      + congruence.
      + congruence.
      + congruence.
      + congruence.
      + try now exists s.
  Qed.

  Theorem finsat_reduction_2 R :
    FSAT (finsat_formula R) -> dPCPb R.
  Proof.
    intros H.
    - destruct H as (D & (I & rho & HF & HE & (((((((((((((((((H1 & H2) & H3) & H4) &
                     H5) & H6) & H7) & H8) & H9) & H10) & H11) & H12) & H13) & H14) & H15) & H16) & H17) & s & H18))).
      cbn in *.
      eapply P_BPCP with (x:=s); trivial; unfold not in *; cbn in *.
      + intros [|]. apply H4. apply H5.
      + intros [|] [|] d1 d2 Hi1 Hi2.
        1: split; try easy; now apply H6.
        3: split; try easy; now apply H7.
        all: exfalso. 2: apply H13 in Hi2. all: destruct (H8 _ _ Hi2) as [Hi3 Hi4]. all:easy.
      + intros [|]. apply H9. apply H10.
      + intros d1 d2 [|]. apply H15. apply H16.
      + cbn in H11. intros x y H. specialize (H11 x y H).
        apply list_or_spec in H11 as [c[[[u v][<- HR]] % in_map_iff [H'|[a[b H']]]]].
        * left. exists u, v. split; trivial. cbn in H'. rewrite !tprep_eval in H'. apply H'.
        * right. exists u, v, a, b. split; trivial. cbn in H'. rewrite !tprep_eval in H'. tauto.
  Qed.

  Theorem FSATd_reduction R :
    dPCPb R <-> FSATd (finsat_formula R).
  Proof.
    split; intros H. 1: now apply finsat_reduction_1.
    destruct H as (D & I & rho & Hlis & Hdis & HH).
    apply finsat_reduction_2. exists D, I, rho. now split.
  Qed.

  Theorem FSAT_reduction R :
    dPCPb R <-> FSAT (finsat_formula R).
  Proof.
    split; intros H. 2: now apply finsat_reduction_2.
    destruct (finsat_reduction_1 H) as (D & I & rho & Hlis & Hdis & HH).
    exists D, I, rho. now split.
  Qed.

  Theorem FSATdc_reduction R :
    dPCPb R <-> FSATdc (exist _ (finsat_formula R) (finsat_closed R)).
  Proof.
    split; intros H. 1: now apply finsat_reduction_1.
    destruct H as (D & I & rho & Hlis & Hdis & HH).
    apply finsat_reduction_2. exists D, I, rho. now split.
  Qed.

End Reduction.
