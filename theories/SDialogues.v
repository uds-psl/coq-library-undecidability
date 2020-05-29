(** *** Translating LJD into S-Vaidity *)

From Undecidability.FOL  Require Export DecidableEnumerable.
From Undecidability.FOLC Require Export WFexp.
From Equations Require Import Equations.

Ltac resolve_existT :=
  match goal with
  | [ H2 : existT _ _ _ = existT _ _ _ |- _ ] => apply (Eqdep.EqdepTheory.inj_pair2 _ _ _ _ _ ) in H2
  | _ => idtac
  end.

Ltac inv H := inversion H; subst; repeat (progress resolve_existT); subst.
Ltac capply H := eapply H; try eassumption.

(** **** S-Dialogues *)

Definition ocons X (o : option X) A :=
  match o with
  | Some a => a :: A
  | None => A
  end.
Infix "o::" := ocons (at level 55).

Lemma ocons_sub X (a : option X) A B :
  A <<= B -> a o:: A <<= a o:: B.
Proof.
  intros H. destruct a; cbn.
  - intros y []; subst; intuition.
  - assumption.
Qed.

Lemma ocons_sub' X (a : option X) A B :
  A <<= B -> A <<= a o:: B.
Proof.
  intros H. destruct a; cbn.
  - intros y H'; right; now apply H.
  - assumption.
Qed.

Class rule_set (f : Type) :=
  {
    atomic : f -> Type ;
    attack : f -> option f -> Type ;
    defense : forall phi adm, attack phi adm -> f -> Type ;
    dec_f : eq_dec f
  }.

Definition opred X (p : X -> Type) (o : option X) : Type :=
  forall x, o = Some x -> p x.

Section SDialogues.
  Variable f : Type.
  Variable R : rule_set f.

  Definition justified A phi := atomic phi -> phi el A.

  Lemma justified_weak A B phi :
    justified A phi -> A <<= B -> justified B phi.
  Proof.
    intros Hjust Hsub Hin. intuition.
  Qed.

  Inductive challenge : Type :=
    C phi adm : attack phi adm -> challenge.
  Inductive opening phi : list f -> challenge -> Type :=
    OP (H : justified nil phi) adm (atk : attack phi adm) : opening phi (adm o:: nil) (C atk).

  Definition deferred : Type := challenge * challenge.
  Definition sstate : Type := list f * list f * list deferred.

  Inductive spmove : sstate -> challenge  -> sstate -> Type :=
  | SPAtk pA oA ds c phi adm (atk : attack phi adm) :
      phi el oA -> opred (justified oA) adm -> spmove (pA, oA, ds) c (adm o:: pA, oA, (C atk, c) :: ds)
  | SPDef pA oA ds phi adm (atk : attack phi adm) psi :
      defense atk psi -> justified oA psi -> spmove (pA, oA, ds) (C atk) (psi :: pA, oA, ds).

  Inductive somove : sstate -> sstate -> challenge -> Type :=
  | SODef pA oA ds c phi adm (atk : attack phi adm) psi :
      defense atk psi -> somove (pA, oA, (C atk, c) :: ds) (pA, psi :: oA, ds) c
  | SOAtk pA phi pA' oA ds adm (atk : attack phi adm) :
      somove (pA ++ phi :: pA', oA, ds) (pA ++ pA', adm o:: oA, ds) (C atk).

  Inductive swin_strat s c : Type :=
    SWS s' : spmove s c s' -> (forall s'' c', somove s' s'' c' -> swin_strat s'' c') -> swin_strat s c.

  Definition svalid phi :=
    prod (justified nil phi) (forall A c, opening phi A c -> swin_strat (nil, A, nil) c).

  (** **** LJD and DLift *)

  Inductive Dprv (A : list f) (T : f -> Type): Type :=
    Def phi :
      T phi ->
      justified A phi ->
      (forall adm (atk : attack phi adm), Dprv (adm o:: A) (defense atk)) ->
      Dprv A T
  | Att psi adm (atk : attack psi adm) :
      psi el A ->
      (forall chi, defense atk chi -> Dprv (chi :: A) T) ->
      opred (fun a => justified A a) adm ->
      opred (fun a => forall adm' (atk' : attack a adm'), Dprv (adm' o:: A) (defense atk')) adm ->
      Dprv A T.
  Notation "A '⊢D' T" := (Dprv A T) (at level 30).

  Definition Dchallenge A (c : challenge) :=
    match c with
    | C c => Dprv A (defense c)
    end.

  Definition Dadmission A phi :=
    forall adm (c : attack phi adm), Dchallenge (adm o:: A) (C c).

  Definition Ddeferred A (d : deferred) :=
    match d with
    | (C a, c) => forall psi, defense a psi -> Dchallenge (psi :: A) c
    end.

  Inductive Dlift : Type :=
  | DlC A c : Dchallenge A c -> Dlift
  | DlA A phi : Dadmission A phi -> Dlift
  | DlD A d : Ddeferred A d -> Dlift.

  Definition Dlift_le' (y x : Dlift) : Prop :=
    match x with
    | @DlC A (@C phi adm c) prv =>
      match prv with
      | Def _ _ Hsub => y = DlA Hsub
      | @Att _ _ _ (Some psi) a Hpsi Hdef Hjust Hadm => y = @DlD A (C a, C c) Hdef \/ y = DlA (Hadm psi eq_refl)
      | @Att _ _ _ None a Hpsi Hdef Hjust Hadm => y = @DlD A (C a, C c) Hdef
      end
    | DlA prv => exists adm c, y = DlC (prv adm c)
    | @DlD A (C a, c) prv => exists psi (H : defense a psi), y = DlC (prv psi H)
    end.
  Definition Dlift_le := tlexp Dlift_le'.

  Infix "⪍" := Dlift_le (at level 40).
  Infix "⪍'" := (lexp Dlift_le') (at level 40).


  Lemma Dlift_le_wf :
    well_founded Dlift_le.
  Proof.
    apply well_founded_tlexp.
    assert (forall A T (prv : Dprv A T) phi adm (c : attack phi adm) (H : T = defense c),
               Acc Dlift_le' (@DlC A (C c) (eq_rect T (fun x => Dprv A x) prv _ H))).
    {
      intros A T H. induction H; intros tau adm' c Hc; subst; constructor; intros y.
      - cbn; intros ?; subst. constructor. intros z (adm & atk & ?); subst.
        apply (H adm atk _ adm atk eq_refl).
      - destruct adm; [intros [|] | intros]; cbn in *. all: subst.
        + constructor; intros z (phi & adm & ?); subst; apply (H phi adm tau adm' c eq_refl).
        + constructor; intros z (adm & c' & ?); subst; apply (H0 f0 eq_refl adm c' f0 adm c' eq_refl).
        + constructor; intros z (phi & adm & ?); subst; apply (H phi adm tau adm' c eq_refl).
    }
    intros [A [phi adm atk] prv | A phi prv | A [[phi adm a] [psi adm' c]] prv].
    - apply (H _ _ prv _ _ atk eq_refl).
    - constructor; intros ? (? & c & ?); subst; apply (H _ _ (prv _ c) _ _ c eq_refl).
    - constructor; intros ? (tau & Htau & ?); subst. apply (H _ _ (prv _ Htau) _ _ c eq_refl).
  Qed.

  (** **** The transformation procedure *)

  Fixpoint IVec (X : Type) (P : X -> Type) (A : list X) : Type :=
    match A with
    | nil => True
    | a :: A' => prod (P a) (IVec P A')
    end.

  Fixpoint vmap (X Y : Type) (P : X -> Type) (A : list X) (f : forall x, P x -> Y) :
    IVec P A -> list Y :=
    match A with
    | nil => fun _ => nil
    | a :: A' => fun v => match v with
                       (x, v') => f a x :: vmap f v'
                     end
    end.

  Fixpoint vapp (X : Type) (P : X -> Type) (A B : list X) :
    IVec P A -> IVec P B -> IVec P (A ++ B):=
    match A with
    | nil => fun _ v2 => v2
    | a :: A' => fun v1 v2 => match v1 with (x, v1') => (x, vapp v1' v2) end
    end.

  Lemma vapp_vmap (X Y : Type) (P : X -> Type) (A B : list X) (g : forall x, P x -> Y)
                  (v : IVec P A) (v' : IVec P B) :
    vmap g (vapp v v') = vmap g v ++ vmap g v'.
  Proof.
    induction A. 2: destruct v; cbn; rewrite IHA. all: reflexivity.
  Qed.

  Fixpoint vsplit (X : Type) (P : X -> Type) a (A B : list X) :
    forall (v : IVec P (A ++ a :: B)), sigT (fun (v1 : IVec P A) => sigT (fun (v2 : IVec P B ) =>
          sig (fun (p : P a) => v = vapp v1 ((p, v2) : IVec P (a :: B))))).
  Proof.
    induction A; cbn.
    - intros [p v2]. now exists I, v2, p.
    - intros [p v]. destruct (IHA v) as (v1 & v2 & p' & ->).
      now exists (p, v1), v2, p'.
  Defined.

  Section Up.
    Variable (X Y Z : Type) (P : list X -> Y -> Type).
    Variable (g : forall A y, P A y -> Z).

    Definition Up A y : Type :=
      sigT (fun B => prod (B <<= A) (P B y)).

    Definition upL A B (H : A <<= B) y (H' : Up A y) : Up B y :=
      match H' with
        (existT _ D (H'', p)) => existT _ D (incl_tran H'' H, p)
      end.

    Definition upI A y (H : P A y) : Up A y :=
      existT _ A (incl_refl A, H).

    Definition up A y (H : Up A y) : Z :=
      match H with existT _ B (_, p) => g p end.

    Lemma up_upL A B (H : A <<= B) y (H' : Up A y) :
      up (upL H H') = up H'.
    Proof. now destruct H' as (? & ? & ?). Qed.

    Lemma up_upI A y (H : P A y) :
      up (upI H) = g H.
    Proof. reflexivity. Qed.
  End Up.

  Arguments up {_ _ _ _} g A.

  Definition Dadmission' := Up Dadmission.
  Definition DlA' a := up DlA a.
  Definition DlA'' A B (C : IVec (Dadmission' A) B) : list Dlift := vmap (@DlA' A) C.

  Definition Ddeferred' := Up Ddeferred.
  Definition DlD' d := up DlD d.
  Definition DlD'' A B (C : IVec (Ddeferred' A) B) : list Dlift := vmap (@DlD' A) C.

  Definition Dchallenge' := Up Dchallenge.
  Definition DlC' c := up DlC c.

  Fixpoint upV (X Y : Type) (P : list X -> Y -> Type) A B (H : A <<= B) D : IVec (Up P A) D -> IVec (Up P B) D :=
    match D with
    | nil => fun v => I
    | d :: D => fun v => match v with (u, v') => (upL H u, upV H v') end
    end.

  Lemma vmap_upV (X Y Z : Type) (P : list X -> Y -> Type) A B C (v : IVec (Up P B) A)
        (g : forall A y, P A y -> Z) (H : B <<= C) :
    vmap (up g C) (upV H v) = vmap (up g B) v.
  Proof.
    induction A.
    - reflexivity.
    - destruct v. cbn. now rewrite IHA, up_upL.
  Qed.

  (** Tactics to simply claims involving vector expressions and liftings **)
  Ltac vsimpl' := repeat (cbn; unfold DlC', DlD', DlA', DlD'', DlA'';
                          try rewrite vmap_upV; try rewrite up_upL; try rewrite up_upI;
                          try rewrite vapp_vmap; try rewrite <- app_assoc).
  Ltac vsimpl := vsimpl'; fold DlC' DlD' DlA' DlD'' DlA''.

  (** Tactics to automatically build the lifted terms and vectors as required in Dprv_swin **)
  Ltac go :=
    lazymatch goal with
    | |- IVec ?P (?a :: ?A) =>
      eapply pair; fold IVec; try go
    | |- IVec ?P (?A ++ ?B) =>
      eapply vapp; fold IVec; try go
    | H : Up ?P (?a :: ?A) ?y  |- Up ?P (?a :: ?B) ?y =>
      eapply upL; [| apply H]; now apply incl_shift
    | H : Up ?P (?a o:: ?A) ?y  |- Up ?P (?a o:: ?B) ?y =>
      eapply upL; [| apply H]; now apply ocons_sub
    | H : Up ?P ?A ?y  |- Up ?P (?a :: ?B) ?y =>
      eapply upL; [| apply H]; now apply incl_tl
    | H : Up ?P ?A ?y  |- Up ?P (?a o:: ?B) ?y =>
      eapply upL; [| apply H]; now apply ocons_sub'
    | H : IVec (?P (?a :: ?A)) ?y  |- IVec (?P (?a :: ?B)) ?y =>
      eapply upV; [| apply H]; now apply incl_shift
    | H : IVec (?P (?a o:: ?A)) ?y  |- IVec (?P (?a o:: ?B)) ?y =>
      eapply upV; [| apply H]; now apply ocons_sub
    | H : IVec (?P ?A) ?y  |- IVec (?P (?a :: ?B)) ?y =>
      eapply upV; [| apply H]; now apply incl_tl
    | H : IVec (?P ?A) ?y  |- IVec (?P (?a o:: ?B)) ?y =>
      eapply upV; [| apply H]; now apply ocons_sub'
    | _ => idtac
    end.
  Ltac build_term := unfold Dchallenge', Dadmission', Ddeferred' in *; go.

  (** A tactic to automatically lift subterms of Dprv into the various liftings **)
  Ltac wrap_up t :=
    let ty := type of t in let ty' := eval simpl in ty in let H := fresh in
    match ty' with
    | Dprv ?A (defense ?atk) => pose (H := @upI _ _ Dchallenge A (C atk) t)
    | Dchallenge ?A ?c => pose (H := upI t)
    | forall a b, Dprv ?A ?T => pose (H := @upI _ _ Dadmission _ _ t)
    | forall a, defense ?b _ -> Dprv _ (defense ?c) => pose (H := @upI _ _ Ddeferred _ (C b, C c) t)
    end.

  (** Tactics to ease solving about ⪍ claims **)
  Ltac build_prefix' HA Ha HB t n :=
    lazymatch n with
    | O =>
      lazymatch t with
      | ?a :: ?B => pose (HA := nil : list Dlift); pose (Ha := a); pose (HB := B)
      | _ => fail "The term was" t
      end
    | S ?n' =>
      lazymatch t with
      | ?a :: ?B =>
        let HA' := fresh
        in build_prefix' HA' Ha HB B n'; pose (HA := a :: HA'); unfold HA' in HA; clear HA'
      | ?A ++ ?B =>
        let HA' := fresh
        in build_prefix' HA' Ha HB B n';
           lazymatch eval unfold HA' in HA' with
           | nil => pose (HA := A); clear HA'
           | _ => pose (HA := A ++ HA'); unfold HA' in HA; clear HA'
           end
      end
    end.

  Ltac build_prefix HA Ha HB n :=
    lazymatch goal with
    | |- _ ⪍ ?A => build_prefix' HA Ha HB A n
    end.

  Ltac solve_Dlift_le :=
    lazymatch goal with
    | |- Forall _ nil => constructor
    | |- Forall _ (_ :: _) => constructor; [try reflexivity | solve_Dlift_le]
    end.

  (** Direct the steps taken in the ⪍ relation.

      step n Y means "take a step in the value at index n, resulting in the new values Y".
   **)
  Ltac step n Y :=
    let HA := fresh in
    let HB := fresh in
    let Ha := fresh in
        build_prefix HA Ha HB n; apply tone; exists HA, HB, Y, Ha; unfold HA, Ha, HB; split; [| split];
        [ cbn; try rewrite! app_assoc; reflexivity | solve_Dlift_le | cbn ].

  (** Apply permp to the 0-th index n times **)
  Ltac permc n :=
    cbn; lazymatch n with
         | O => reflexivity
         | S ?n' => permp 0; permc n'
         end.

  Lemma Dprv_swin P :
    forall pA oA D c (DpA : IVec (Dadmission' oA) pA) (DD : IVec (Ddeferred' oA) D) (Dc : Dchallenge' oA c),
      P = DlC' Dc :: DlA'' DpA ++ DlD'' DD -> swin_strat (pA, oA, D) c.
  Proof.
    induction (Dlift_le_wf P). intros; subst. destruct Dc as (oA' & HoA' & Dc), c. dependent elimination Dc.
    - apply SWS with (s' := (phi0 :: pA, oA, D)). 1: capply SPDef; eapply (justified_weak j HoA').
      wrap_up d0. intros ? ?; inversion 1; subst.
      + destruct DD as [(oA'' & HoA'' & Hdef) DD2]. wrap_up (Hdef _ X1).
        eapply X. 2: reflexivity. Unshelve. 2-4: build_term. vsimpl. etransitivity.
        2: step 0 [DlA' H0]; reflexivity. step 2 [DlC' H1]. 1: now exists psi, X1. permc 2.
      + destruct pA0; cbn in *; inversion H2; subst.
        * wrap_up (d0 adm0 atk). eapply X. 2: reflexivity. Unshelve. 2-4: build_term.
          vsimpl; etransitivity. 2: step 0 [DlA' H0]; reflexivity.
          step 0 [DlC' H1]. now exists adm0, atk. permc 1.
        * destruct (vsplit DpA) as (DpA1 & DpA2 & def & ->). destruct def as (oA'' & HoA'' & Hdef).
          wrap_up (Hdef adm0 atk). eapply X. 2: reflexivity. Unshelve. 2-4: build_term. vsimpl; etransitivity.
          2: step 0 [DlA' H0]; reflexivity. step 2 [DlC' H1]. now exists adm0, atk. permc 1.
    - apply SWS with (s' := (adm0 o:: pA, oA, (C atk, C a) :: D)).
      1: capply SPAtk; [now apply HoA' | intros x ->; now apply (justified_weak (o x eq_refl))].
      intros ? ? H''; inv H''; subst.
      + wrap_up (d1 _ X0); wrap_up d1. destruct adm0; cbn.
        * wrap_up (o0 f0 eq_refl). eapply X. 2: reflexivity. Unshelve. 2-4: build_term.
          vsimpl; etransitivity. 2: step 0 (DlD' H1 :: DlA' H2 :: nil); [left | right|]; reflexivity.
          step 0 [DlC' H0]. now exists psi0, X0. reflexivity.
        * eapply X. 2: reflexivity. Unshelve. 2-4: build_term. vsimpl; etransitivity.
          2: step 0 [DlD' H1]; reflexivity. step 0 [DlC' H0]. now exists psi0, X0. reflexivity.
      + destruct adm0;[destruct pA0 |]; cbn in H1; cbn; subst; try inv H1.
        * wrap_up (o0 f0 eq_refl adm1 atk0). wrap_up d1. wrap_up (o0 f0 eq_refl).
          eapply X. 2: reflexivity. Unshelve. 2-4: build_term. vsimpl; etransitivity.
          2: step 0 (DlD' H2 :: DlA' H3 :: nil); [left | right|]; reflexivity. step 1 [DlC' H0].
          now exists adm1, atk0. permp 0. permp 1.  reflexivity.
        * destruct (vsplit DpA) as (DpA1 & DpA2 & (oA'' & HoA'' & Hdef) & ->).
          wrap_up (Hdef adm1 atk0). wrap_up (o0 f0 eq_refl). wrap_up d1.
          eapply X. 2: reflexivity. Unshelve. 2-4: build_term. vsimpl; etransitivity.
          2: step 0 (DlD' H3 :: DlA' H2 :: nil); [left | right|]; reflexivity.
          step 3 [DlC' H0]. now exists adm1, atk0. permp 0. permp 0. permp 2. reflexivity.
        * destruct (vsplit DpA) as (DpA1 & DpA2 & (oA'' & HoA'' & Hdef) & ->).
          wrap_up (Hdef adm1 atk0). wrap_up d1. eapply X. 2: reflexivity. Unshelve. 2-4: build_term.
          vsimpl; etransitivity. 2: step 0 [DlD' H1]; reflexivity. step 2 [DlC' H0]. now exists adm1, atk0.
          permp 0. permp 2. reflexivity.
  Qed.
End SDialogues.
