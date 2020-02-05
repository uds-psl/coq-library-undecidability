(** * Trakhtenbrot's Theorem *)

Require Import Equations.Equations.
Require Import Lia.

From Undecidability Require Import Problems.PCP.
From Undecidability Require Import Problems.FOLFS.



(** ** Bounded boolean strings *)

Derive Signature for le.

Lemma le_irrel' n :
  forall H : n <= n, H = le_n n.
Proof.
  induction n; depelim H.
  - reflexivity.
  - assert (H = eq_refl) as -> by apply Eqdep_dec.UIP_refl_nat.
    cbn in H1. assumption.
  - exfalso. lia.
Qed.

Lemma le_irrel k l :
  forall H1 H2 : k <= l, H1 = H2.
Proof.
  induction l; depelim H1.
  - intros H2. now rewrite le_irrel'.
  - intros H2. now rewrite le_irrel'.
  - depelim H2; try apply le_irrel'. f_equal. apply IHl.
Qed.

Definition bstring n :=
  { s : string bool | |s| <= n}.

Lemma string_nil (s : string bool) :
  |s| <= 0 <-> s = nil.
Proof.
  destruct s; cbn.
  - split; trivial; lia.
  - split; try congruence. intros H. depelim H.
Qed.

Definition bnil n :
  bstring n.
Proof.
  exists nil. cbn. lia.
Defined.

Definition bcons n (b : bool) :
  bstring n -> bstring (S n).
Proof.
  intros [s H]. exists (b::s). cbn. lia.
Defined.

Lemma bstring_eq n (s t : bstring n) :
  proj1_sig s = proj1_sig t <-> s = t.
Proof.
  split; try now intros ->.
  destruct s as [s H1], t as [t H2]; cbn.
  intros ->. now rewrite (le_irrel H1 H2).
Qed.

Lemma bstring_eq' n (s t : bstring n) :
  proj1_sig s = proj1_sig t -> s = t.
Proof.
  apply bstring_eq.
Qed.

Definition bstring_step n (L : list (bstring n)) :=
  [bnil (S n)] ++ map (bcons true) L ++ map (bcons false) L.

Definition bcast n s (H : |s| <= n) : bstring n :=
  exist _ _ H.

Lemma listable_bstring' n :
  { L | forall s : bstring n, s el L }.
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

Lemma listable_bstring n :
  listable (bstring n).
Proof.
  exists (proj1_sig (listable_bstring' n)). apply proj2_sig.
Qed.

Definition obstring n :=
  option (bstring n).

Lemma listable_obstring' n :
  { L | forall s : obstring n, s el L }.
Proof.
  destruct (listable_bstring' n) as [L HL]. exists (None :: map Some L).
  intros [x|]; trivial. right. apply in_map, HL.
Qed.

Lemma listable_obstring n :
  listable (obstring n).
Proof.
  exists (proj1_sig (listable_obstring' n)). apply proj2_sig.
Qed.




(** ** Signature used in the proof *)

Inductive finsat_Funcs :=
| f : bool -> finsat_Funcs
| e : finsat_Funcs
| dum : finsat_Funcs.

Inductive finsat_Preds :=
| P : finsat_Preds
| less : finsat_Preds
| equiv : finsat_Preds.

Definition finsat_fun_ar func :=
  match func with   
  | f b => 1
  | e => 0
  | dum => 0
  end.

Definition finsat_pred_ar pred :=
  match pred with   
  | P => 2
  | less => 2
  | equiv => 2
  end.

Instance finsat_sig : Signature :=
  {| Funcs := finsat_Funcs ;
     fun_ar := finsat_fun_ar ;
     Preds := finsat_Preds ;
     pred_ar := finsat_pred_ar |}.
  

Definition i_f domain {I : interp domain} : bool -> domain -> domain :=
  fun b x => (FullTarski.i_f (f := f b)) (Vector.cons x Vector.nil).

Definition i_e domain {I : interp domain} : domain :=
  (FullTarski.i_f (f := e)) Vector.nil.

Definition i_P domain {I : interp domain} : domain -> domain -> Prop :=
  fun x y => (FullTarski.i_P (P := P)) (Vector.cons x (Vector.cons y Vector.nil)).

Notation i_equiv x y :=
  ((FullTarski.i_P (P := equiv)) (Vector.cons x (Vector.cons y Vector.nil))).

Fixpoint iprep domain {I : interp domain} (x : list bool) (y : domain) :=
  match x with
  | nil => y
  | b::x => i_f b (iprep x y)
  end.

Definition ienc domain {I : interp domain} (x : list bool) := iprep x i_e.




(** ** Finite standard models *)

Section FIB.
  
  Variable R : BSRS.

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
  Proof.
    split.
    - intros []; cbn.
      + intros v. exact (ccons b (Vector.hd v)).
      + intros _. exact (Some (bnil n)).
      + intros _. exact None.
    - intros []; cbn.
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
    unfold ienc. cbn. cbn. erewrite obstring_iprep.
    f_equal. apply bstring_eq, app_nil_r.
    Unshelve. rewrite app_length. cbn. lia.
  Qed.

  Lemma obstring_ienc' n s (H : ~ |s| <= n) :
    @ienc _ (FIB n) s = None.
  Proof.
    induction s; cbn in *; try lia.
    change (@ccons n a (ienc s) = None).
    destruct (le_dec (|s|) n) as [H'|H'].
    - rewrite (obstring_ienc H'). cbn.
      destruct le_dec; tauto.
    - now rewrite IHs.
  Qed.

  Lemma crdv_iff n (x y : obstring n) :
    i_P x y <-> exists s t, derivable R s t /\ x = ienc s /\ y = ienc t /\ |s| <= n /\ |t| <= n.
  Proof.
    destruct x as [ [x HX]|], y as [ [y HY]|]; split; cbn; auto.
    { intros H. exists x, y. repeat erewrite obstring_ienc. now repeat split. }
    all: intros (s&t&H1&H2&H3&H4&H5). all: try unshelve erewrite obstring_ienc in H2, H3; auto.
    all: try discriminate. depelim H2. depelim H3. assumption.
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
    - repeat unshelve erewrite obstring_ienc; trivial; lia.
    - rewrite (obstring_ienc H), (obstring_ienc' H'). cbn. tauto.
    - rewrite (obstring_ienc' H). cbn. tauto.
    - rewrite (obstring_ienc' H). cbn. tauto.
  Qed.

  Lemma drv_cdrv s t :
    derivable R s t <-> @cdrv (max (|s|) (|t|)) (ienc s) (ienc t).
  Proof.
    repeat unshelve erewrite obstring_ienc; try reflexivity; lia.
  Qed.

  Lemma drv_cdrv' s :
    derivable R s s <-> @cdrv (|s|) (ienc s) (ienc s).
  Proof.
   repeat unshelve erewrite obstring_ienc; try reflexivity; lia.
  Qed.

  Lemma BPCP_P :
    BPCP' R <-> exists n x, @i_P _ (FIB n) x x.
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
      intros _ H. depelim H. split; trivial. f_equal. now apply bstring_eq.
    Qed.

    Lemma None_dec X (x : option X) :
      {x = None} + {x <> None}.
    Proof.
      destruct x; auto. right. discriminate.
    Qed.

    Lemma FIB_HF2'  x y : 
      i_f true x = i_f false y -> i_f true x = None /\ i_f false y = None.
    Proof.
      intros H. destruct (None_dec (i_f true x)), (None_dec (i_f false y)); try tauto; exfalso.
      - symmetry in H. specialize (FIB_HF2 n0 H). congruence.
      - specialize (FIB_HF2 n0 H). congruence.
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
      - left. exists x, y. repeat erewrite obstring_ienc. repeat split; trivial.
      - assert (HU : |u| <= n). { rewrite app_length in HX. lia. }
        assert (HV : |v| <= n). { rewrite app_length in HY. lia. }
        destruct x as [|b x], y as [|c y].
        + cbn. apply IHderivable.
        + right. exists [], (c::y), (obcast HU), (obcast HV).
          repeat erewrite obstring_iprep. repeat split; trivial.
          right. left. repeat split; eauto using app_neq. f_equal. now apply bstring_eq.
        + right. exists (b::x), [], (obcast HU), (obcast HV).
          repeat erewrite obstring_iprep. repeat split; trivial.
          left. repeat split; eauto using app_neq. f_equal. now apply bstring_eq.
        + right. exists (b::x), (c::y), (obcast HU), (obcast HV).
          repeat erewrite obstring_iprep. repeat split; trivial.
          right. right. repeat split; eauto using app_neq.
    Qed.

  End Ax.

End FIB.



(** ** Decidability of standard models *)

Section CdrvDec.

  Section CdrvDec'.

  Variable X : Type.
  Variable R : stack X.

  (* cdrv is decidable *)

  Fixpoint derivations n :=
    match n with
    | O => R
    | S n => derivations n ++
            flat_map (fun p => [(fst p ++ fst q) / (snd p ++ snd q) | q ∈ derivations n]) R
    end.

  Lemma derivations_drv n s t :
    s/t el derivations n -> derivable R s t.
  Proof.
    revert s t. induction n; intros s t.
    - cbn. now constructor.
    - intros [H|H] % in_app_iff; try now apply IHn.
      apply in_flat_map in H as [ [u v] [H1 H2] ]. fold derivations in H2.
      apply in_map_iff in H2 as [ [u' v'] [H2 H3] ].
      injection H2. intros <- <-. constructor 2; trivial. now apply IHn.
  Qed.

  Lemma derivations_cum :
    cumulative (derivations).
  Proof.
    intros n. cbn. eauto.
  Qed.

  Hint Resolve derivations_cum.

  Lemma derivations_S s t u v n :
    s/t el R -> u/v el derivations n -> (s++u)/(t++v) el derivations (S n).
  Proof.
    intros H1 H2.
    apply in_app_iff; fold derivations. right.
    apply in_flat_map. exists (s/t). split; trivial.
    apply in_map_iff. now exists (u/v).
  Qed.        

  Lemma drv_derivations s t :
    derivable R s t -> s/t el derivations (|s| + |t|).
  Proof.
    induction 1.
    - apply (cum_ge' (n:=0)); trivial. lia.
    - destruct x as [|b x], y as [|c y]; trivial; rewrite !app_length.
      all: apply (cum_ge' (n:=S(|u|+|v|))); trivial.
      all: try (cbn; lia). all: now apply derivations_S.
  Qed.

  End CdrvDec'.

  Variable R : BSRS.

  Definition cdrv_dec n s t :
    dec (@cdrv R n s t).
  Proof.
    destruct s as [ [s HT]|], t as [ [t HS]|]; cbn; auto.
    destruct (list_in_dec (s/t) (derivations R (|s| + |t|)) _) as [H|H].
    - left. apply (derivations_drv H).
    - right. intros H'. apply H, drv_derivations, H'.
  Defined.

  (* sub is decidable *)

  Inductive subi s : string bool -> Prop :=
  | subi1 : subi s s
  | subi2 t b : subi s t -> subi s (b::t).

  Definition subi_dec s t :
    dec (subi s t).
  Proof.
    induction t.
    - destruct s.
      + left. constructor.
      + right. inversion 1.
    - destruct (IHt) as [H|H].
      + left. now constructor.
      + assert (dec (s = a::t)) as [->|H1] by eauto.
        * left. constructor.
        * right. inversion 1; subst; eauto.
  Qed.

  Lemma subi_sub s t :
    subi s t <-> exists s' : list bool, t = s' ++ s.
  Proof.
    split.
    - induction 1.
      + now exists nil.
      + destruct IHsubi as [s' ->]. now exists (b::s').
    - intros [s' ->]. induction s'; now constructor.
  Qed.

  Definition sub_dec n s t :
    dec (@sub n s t).
  Proof.
    destruct s as [ [s HT]|], t as [ [t HS]|]; cbn; auto.
    apply and_dec; eauto. apply (dec_transfer (@subi_sub s t)), subi_dec.
  Qed.

  Instance bstring_discrete n (s t : bstring n) :
    dec (s = t).
  Proof.
    destruct s as [s Hs], t as [t Ht].
    decide (s = t) as [<-|H].
    - left. f_equal. apply le_irrel.
    - right. intros H'. congruence.
  Qed.

  Definition obstring_discrete n (s t : obstring n) :
    dec (s = t).
  Proof.
    exact _.
  Qed.

  Definition FIB_dec n rho phi :
    dec (sat _ _ (@FIB R n) rho phi).
  Proof.
    destruct (listable_obstring' n) as [L HL].
    induction phi in rho |- *; eauto.
    - destruct P0; cbn.
      + apply cdrv_dec.
      + apply sub_dec.
      + apply obstring_discrete.
    - destruct (@list_forall_dec (obstring n) L (fun x => sat _ _ (@FIB R n) (x .: rho) phi)) as [H|H].
      + intros s. apply IHphi.
      + left. intros x. apply H, HL.
      + right. intros H'. apply H.
        intros s _. apply H'.
    - destruct (@list_exists_dec (obstring n) L (fun x => sat _ _ (@FIB R n) (x .: rho) phi)) as [H|H].
      + intros s. apply IHphi.
      + left. destruct H as [s H]. exists s. apply H.
      + right. intros [s H']. apply H.
        exists s. split; trivial.
  Qed.

  Lemma FIB_decidable n rho :
    decidable (fun phi => sat _ _ (@FIB R n) rho phi).
  Proof.
    apply decidable_iff. constructor. apply FIB_dec.
  Qed.

End CdrvDec.




(** ** Axiomatisation of finite standard models *)

Section Conv.
  
  Variable R : BSRS.
  
  Variable D : Type. 
  Hypothesis HD : listable D.

  Variable I : interp D.

  Notation sub x y :=
    ((FullTarski.i_P (P := less)) (Vector.cons x (Vector.cons y Vector.nil))).

  Notation dum :=
    ((FullTarski.i_f (f := dum)) Vector.nil).

  Hypothesis HP : forall x y, i_P x y -> x <> dum /\ y <> dum.

  Hypothesis HS1 : forall x, ~ sub x x.
  Hypothesis HS2 : forall x y z, sub x y -> sub y z -> sub x z.

  Hypothesis HF1 : forall b x, i_f b x <> i_e.
  Hypothesis HF2 : forall b1 b2 x y, i_f b1 x <> dum -> i_f b1 x = i_f b2 y -> x = y /\ b1 = b2.
  Hypothesis HF3 : forall b x, i_f b x <> dum -> x <> dum.

  Hypothesis HI :
    forall x y, i_P x y -> (exists s t, s/t el R /\ x = ienc s /\ y = ienc t)
                     \/ (exists s t u v, s/t el R /\ x = iprep s u /\ y = iprep t v /\ i_P u v /\
                                   ((sub u x /\ v = y) \/ (sub v y /\ u = x) \/ (sub u x /\ sub v y))).

  (* Any solution of R that holds in a model satisfying the axioms gives rise to an actual solution. *)
      
  Lemma ienc_inj s t :
    ienc s <> dum -> ienc s = ienc t -> s = t.
  Proof.
    revert t. induction s; intros [|]; cbn; trivial.
    - intros _ H. symmetry in H. now apply HF1 in H.
    - intros _ H. now apply HF1 in H.
    - intros H [H' ->] % HF2; trivial. f_equal.
      apply IHs; trivial. now apply HF3 in H.
  Qed.

  Definition sub' L x y :=
    sub x y /\ x el L.
  
  Lemma sub_acc_pred L x y :
    sub y x -> Acc (sub' L) x -> Acc (sub' L) y.
  Proof.
    intros H H'. constructor. intros z [H1 H2].
    apply H'. split; trivial. now apply (HS2 H1).
  Qed.

  Lemma sub_acc_cons L x y :
    Acc (sub' L) x -> ~ sub y x -> Acc (sub' (y::L)) x.
  Proof.
    induction 1 as [x HX IH]. intros H.
    constructor. intros z [H1[->|H2] ].
    - contradiction.
    - apply IH; firstorder.
  Qed.

  Lemma sub_acc_cons' L x y :
    sub y x -> Acc (sub' L) x -> Acc (sub' (y::L)) y.
  Proof.
    intros H1 H2. apply sub_acc_cons; trivial.
    now apply (sub_acc_pred H1).
  Qed.

  Lemma sub_acc_step L a x :
    Acc (sub' L) x -> Acc (sub' (a::L)) x.
  Proof.
    induction 1 as [x HX IH].
    constructor. intros y [H [->|H'] ].
    - now apply (sub_acc_cons' H).
    - apply IH. now split.
  Qed.

  Lemma sub_acc' L x :
    Acc (sub' L) x.
  Proof.
    induction L.
    - constructor. intros y [_ [] ].
    - apply sub_acc_step, IHL.
  Qed.

  Lemma sub_acc x :
    Acc (fun a b => sub a b) x.
  Proof.
    destruct HD as [L HL].
    induction (sub_acc' L x) as [x _ IH].
    constructor. intros y H. now apply IH.
  Qed.

  Inductive psub : (D * D) -> (D * D) -> Prop :=
  | psub1 x u : sub u x -> forall y, psub (u,y) (x,y)
  | psub2 y u : sub u y -> forall x, psub (x,u) (x,y)
  | psub3 x y u v : sub u x -> sub v y -> psub (u,v) (x,y).

  Lemma psub_acc p :
    Acc psub p.
  Proof.
    destruct p as [x y]. revert y.
    induction (sub_acc x) as [x HX IHX]. intros y.
    induction (sub_acc y) as [y HY IHY]. constructor.
    intros [u v]. inversion 1; subst; auto.
  Qed.

  Lemma ienc_iprep s t :
    iprep s (ienc t) = ienc (s ++ t).
  Proof.
    induction s; cbn; trivial. now rewrite IHs.
  Qed.

  Lemma P_drv' p :
    i_P (fst p) (snd p) -> exists s t, derivable R s t /\ fst p = ienc s /\ snd p = ienc t.
  Proof.
    intros H. induction (psub_acc p) as [ [x' y'] _ IH]; cbn in *.
    destruct (HI H) as [(s&t&H1&H2&H3)|(s&t&u&v&H1&H2&H3&H4&H5)]; subst.
    - exists s, t. repeat split; trivial. now constructor.
    - destruct (IH (u,v)) as (s'&t'&H6&H7&H'); cbn in *; trivial; subst.
      + destruct H5 as [ [H5 <-]|[ [H5 <-]|[] ] ]; eauto using psub.
      + exists (s++s'), (t++t'). rewrite !ienc_iprep. repeat split; trivial. now right.
  Qed.

  Lemma P_drv x y :
    i_P x y -> exists s t, derivable R s t /\ x = ienc s /\ y = ienc t.
  Proof.
    apply P_drv' with (p:=(x,y)).
  Qed.

  Lemma P_BPCP x :
    i_P x x -> BPCP' R.
  Proof.
    intros H. destruct (P_drv H) as (s&t&H1&H2&H3); subst.
    apply ienc_inj in H3 as ->; try apply (HP H). now exists t.
  Qed.

End Conv.




(** ** Axioms stated as a concrete first-order formula *)

Section Reduction.

  Notation "# x" := (var_term x) (at level 2).
  Definition t_f b x := Func (f b) (Vector.cons x Vector.nil).
  Definition t_e := Func e Vector.nil.
  Definition t_dum := Func dum Vector.nil.
  Definition f_P x y := Pred P (Vector.cons x (Vector.cons y Vector.nil)).
  Notation "x ≡ y" := (Pred equiv (Vector.cons x (Vector.cons y Vector.nil))) (at level 20).
  Notation "x ≢ y" := (¬ (x ≡ y)) (at level 20).
  Notation "x ≺ y" := (Pred less (Vector.cons x (Vector.cons y Vector.nil))) (at level 20).

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

  Definition tenc (x : list bool) := tprep x t_e.

  Definition ax_P := ∀ ∀ f_P #1 #0 --> (#1 ≢ t_dum) ∧ (#0 ≢ t_dum).
  Definition ax_S1 := ∀ ¬ (#0 ≺ #0).
  Definition ax_S2 := ∀ ∀ ∀ #2 ≺ #1 --> #1 ≺ #0 --> #2 ≺ #0.

  Definition ax_HF1_true := ∀ t_f true #0 ≢ t_e.
  Definition ax_HF1_false := ∀ t_f false #0 ≢ t_e.
  Definition ax_HF2_true := ∀ ∀ t_f true #1 ≢ t_dum --> t_f true #1 ≡ t_f true #0 --> #1 ≡ #0.
  Definition ax_HF2_false := ∀ ∀ t_f false #1 ≢ t_dum --> t_f false #1 ≡ t_f false #0 --> #1 ≡ #0.
  Definition ax_HF2 := ∀ ∀ t_f true #1 ≡ t_f false #0 --> (t_f true #1 ≡ t_dum ∧ t_f false #0 ≡ t_dum).

  Definition ax_HF3_true := ∀ t_f true #0 ≢ t_dum --> #0 ≢ t_dum.
  Definition ax_HF3_false := ∀ t_f false #0 ≢ t_dum --> #0 ≢ t_dum.

  Definition ax_HI' c :=
    (#1 ≡ tenc (fst c) ∧ #0 ≡ tenc (snd c))
    ∨ (∃ ∃ #3 ≡ tprep (fst c) #1 ∧ #2 ≡ tprep (snd c) #0 ∧ f_P #1 #0
           ∧ ((#1 ≺ #3 ∧ #0 ≡ #2) ∨ (#0 ≺ #2 ∧ #1 ≡ #3) ∨ (#1 ≺ #3 ∧ #0 ≺ #2))).

  Definition ax_HI (R : BSRS) := ∀ ∀ f_P #1 #0 --> list_or (map ax_HI' R).

  Definition finsat_formula (R : BSRS) :=
    ax_P ∧ ax_S1 ∧ ax_S2 ∧ ax_HF1_true ∧ ax_HF1_false ∧ ax_HF2_true ∧ ax_HF2_false
    ∧ ax_HF2 ∧ ax_HF3_true ∧ ax_HF3_false ∧ ax_HI R ∧ ∃ f_P #0 #0.

  (* Verification of the reduction *)

  Theorem finsat_reduction R :
    BPCP' R <-> @finsat finsat_sig equiv eq_refl (finsat_formula R).
  Proof.
    split; intros H.
    - apply BPCP_P in H as [n [s H]]. exists (obstring n), (@FIB R n), (fun _ => None).
      split; try apply listable_obstring. cbn.
      split. apply FIB_decidable.
      split. reflexivity.
      split. apply (@FIB_HP R).
      split. apply FIB_HS1.
      split. apply FIB_HS2.
      split. intros x. apply (@FIB_HF1 R _ true x).
      split. intros x. apply (@FIB_HF1 R _ false x).
      split. intros x y H1 H2. now destruct (FIB_HF2 (R:=R) H1 H2).
      split. intros x y H1 H2. now destruct (FIB_HF2 (R:=R) H1 H2).
      split. apply (@FIB_HF2' R).
      split. intros x. apply (@FIB_HF3 R _ true x).
      split. intros x. apply (@FIB_HF3 R _ false x).
      split; try now exists s. cbn.
      intros u v [[a[b[H1 H2]]]|[a[b[a'[b'[H1 H2]]]]]] % (@FIB_HI R _ u v); apply list_or_spec.
      + exists (ax_HI' (a/b)). split; try now apply in_map.
        left. cbn. now rewrite !tprep_eval.
      + exists (ax_HI' (a/b)). split; try now apply in_map.
        right. exists a', b'. cbn. now rewrite !tprep_eval.
    - destruct H as (D & I & rho & HF & _ & HE & H1 & H2 & H3 & H4 &
                     H5 & H6 & H7 & H8 & H9 & H10 & H11 & s & H12).
      unfold i_eqp in HE. cbn in HE. cbn in *.
      eapply P_BPCP with (x:=s); trivial.
      + cbn in H1. intros x y. specialize (H1 x y). now rewrite !HE in H1.
      + cbn in H4, H5. intros b x. specialize (H4 x). specialize (H5 x).
        rewrite !HE in H4, H5. now destruct b.
      + cbn in H6, H7, H8. intros b1 b2 x y.
        specialize (H6 x y). specialize (H7 x y).
        rewrite !HE in H6, H7. destruct b1, b2; eauto.
        * specialize (H8 x y). rewrite !HE in H8. tauto.
        * specialize (H8 y x). rewrite !HE in H8.
          intros I1 I2. exfalso. symmetry in I2. tauto.
      + cbn in H9, H10. intros b x. specialize (H9 x). specialize (H10 x).
        rewrite !HE in H9, H10. now destruct b.
      + cbn in H11. intros x y H. specialize (H11 x y H).
        apply list_or_spec in H11 as [c[[[u v][<- HR]] % in_map_iff [H'|[a[b H']]]]].
        * left. exists u, v. split; trivial. cbn in H'. now rewrite !tprep_eval, !HE in H'.
        * right. exists u, v, a, b. split; trivial. cbn in H'. now rewrite !tprep_eval, !HE in H'.
  Qed.

End Reduction.

  




  
