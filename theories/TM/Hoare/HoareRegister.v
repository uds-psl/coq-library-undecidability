From Undecidability Require Import Hoare.HoareLogic.
From Undecidability Require Import ProgrammingTools.


(** ** Tape/Register Specification *)

(* Register specifications are deep embeded because this makes it
easier to do computation with the specifications. A tapes
specification is a list of assertions about tapes. Each tape may
contain a value (optionally with size), or be right. *)

Section RegSpec.

  Variable sig : Type.

  (* Notation without EqType stuff *)
  Local Notation "sig '^+'" := ((boundary + sig) % type) (at level 0) : type_scope.

  Inductive RegSpec : Type :=
  | Contains {sigX X : Type} {cX : codable sigX X} (r : Retract sigX sig) : X -> RegSpec
  | Contains_size {sigX X : Type} {cX : codable sigX X} (r : Retract sigX sig) : X -> nat -> RegSpec
  | Void : RegSpec
  | Void_size : nat -> RegSpec
  | Custom : (tape sig^+ -> Prop) -> RegSpec. (** Allows the user to specify the tape manually *)

  (* Semantics *)
  Definition tspec_single (spec : RegSpec) (t : tape sig^+) : Prop :=
    match spec with
    | Contains r x => t ≃(r) x
    | Contains_size r x s => t ≃(r; s) x
    | Void => isVoid t
    | Void_size s => isVoid_size t s
    | Custom p => p t
    end.

  Lemma tspec_single_Contains_size_Contains {sigX X : Type} {cX : codable sigX X} (r : Retract sigX sig) (x : X) (s : nat) (t : tape sig^+) :
    tspec_single (Contains_size r x s) t -> tspec_single (Contains r x) t.
  Proof. cbn. auto. Qed.

  Inductive Spec (n : nat) : Type :=
  | SpecVector : Vector.t (RegSpec) n -> Spec n
  | SpecFalse : Spec n.

  Definition tspec {n : nat} (spec : Spec n) : Assert sig^+ n :=
    match spec with
    | SpecVector spec => fun (t : tapes sig^+ n) => forall (i : Fin.t n), tspec_single spec[@i] t[@i]
    | SpecFalse _ => fun (t : tapes sig^+ n) => False
    end.


  (** Enrich the specification with spaces *)
  Definition withSpace_single (P : RegSpec) (size : nat) :=
    match P with
    | Contains r x => Contains_size r x size
    | Void => Void_size size
    | _ => P
    end.

  Definition withSpace {n : nat} (P : Spec n) (spaces : Vector.t nat n) : Spec n :=
    match P with
    | SpecVector spec => SpecVector (Vector.map2 withSpace_single spec spaces)
    | SpecFalse _ => SpecFalse _
    end.

  (** Drop the spaces *)
  Lemma tspec_single_withSpace_tspec_single (P : RegSpec) (size : nat) t :
    tspec_single (withSpace_single P size) t -> tspec_single P t.
  Proof. intros. destruct P; cbn in *; auto. Qed.

  Lemma tspec_withSpace_tspec {n : nat} (P : Spec n) (s : Vector.t nat n) t :
    tspec (withSpace P s) t -> tspec P t.
  Proof. intros. destruct P; cbn in *; auto. intros i; specialize (H i). simpl_vector in *. eapply tspec_single_withSpace_tspec_single; eauto. Qed.

  (** Invent some dummy spaces *)

  Definition dummy_size (t : tape sig^+) (P : RegSpec) : nat :=
    match P with
    | Contains r x => length (left t)
    | Void => length (tape_local_l t)
    | _ => 0
    end.

  Lemma tspec_single_tspec_single_withSpace (P : RegSpec) t :
    tspec_single P t -> tspec_single (withSpace_single P (dummy_size t P)) t.
  Proof. intros H. destruct P; cbn in *; eauto. Qed.


  Definition dummy_sizes (n : nat) (t : tapes sig^+ n) (P : Spec n) : Vector.t nat n :=
    match P with
    | SpecVector vect => Vector.map2 dummy_size t vect
    | SpecFalse _ => Vector.const 0 n
    end.

  Lemma tspec_tspec_withSpace (n : nat) (P : Spec n) t :
    tspec P t -> tspec (withSpace P (dummy_sizes t P)) t.
  Proof.
    intros; destruct P; cbn in *; auto.
    intros i; specialize (H i); cbn in *. simpl_vector. now apply tspec_single_tspec_single_withSpace.
  Qed.

  (*
  (** Remove the space annotations *)
  Definition removeSpace_reg (P : RegSpec) :=
    match P with
    | Contains_size r x size => Contains r x
    | Void_size size => Void
    | _ => P
    end.

  Lemma tspec_single_removeSpace_reg (P : RegSpec) t :
    tspec_single P t ->
    tspec_single (removeSpace_reg P) t.
  Proof. intros H. destruct P; cbn in *; auto. Qed.

  Definition removeSpace (n : nat) (P : Spec n) :=
    match P with
    | SpecVector spec => SpecVector (Vector.map removeSpace_reg spec)
    | SpecFalse _ => SpecFalse _
    end.

  Lemma tspec_removeSpace (n : nat) (P : Spec n) t :
    tspec P t ->
    tspec (removeSpace P) t.
  Proof.
    intros H; destruct P; cbn; auto.
    intros i; specialize (H i); cbn in *.
    simpl_vector. eapply tspec_single_removeSpace_reg; eauto.
  Qed.
*)

End RegSpec.

Arguments Custom {sig}.
Arguments Void {sig}.
Arguments Void_size {sig}.
Arguments SpecFalse {sig n}.
Arguments dummy_sizes : simpl never.
Hint Resolve tspec_single_Contains_size_Contains : core.

Notation "t ≃≃ S" := (tspec S t) (at level 70, no associativity).




Lemma Triple_SpecFalse {sig : finType} {n : nat} {F : Type} (pM : pTM sig^+ F n) Q :
  Triple (tspec SpecFalse) pM Q.
Proof. cbn. apply Triple_False. Qed.

Lemma TripleT_SpecFalse {sig : finType} {n : nat} {F : Type} (k : nat) (pM : pTM sig^+ F n) Q :
  TripleT (tspec SpecFalse) k pM Q.
Proof. cbn. apply TripleT_False. Qed.

Lemma tspec_not_SpecFalse {sig : Type} {n : nat} (t : tapes (boundary+sig) n) :
  t ≃≃ SpecFalse -> False.
Proof. cbn. auto. Qed.

Lemma tspec_not_SpecFalse_withSpace {sig : Type} {n : nat} (t : tapes (boundary+sig) n) (ss : Vector.t nat n) :
  t ≃≃ withSpace SpecFalse ss -> False.
Proof. cbn. auto. Qed.


Hint Immediate Triple_SpecFalse TripleT_SpecFalse : core.



(* TODO: [SpecFalse] could be defined in the same manner. We could then remove the unhandy [SpecVector] constructor. *)
Definition SpecTrue {sig : Type} {n : nat} : Spec sig n := SpecVector (Vector.const (Custom (fun _ => True)) n).
Arguments SpecTrue : simpl never.

Lemma tspec_SpecTrue {sig : finType} {n : nat} (t : tapes sig^+ n) :
  t ≃≃ SpecTrue.
Proof. cbn. intros i. unfold tspec_single, SpecTrue. cbn. now rewrite Vector.const_nth. Qed.


Lemma tspec_SpecTrue_withSpace {sig : finType} {n : nat} (t : tapes sig^+ n) (ss : Vector.t nat n) :
  t ≃≃ withSpace SpecTrue ss.
Proof. cbn. intros i. unfold tspec_single, SpecTrue. now rewrite nth_map2', Vector.const_nth. Qed.

Hint Immediate tspec_SpecTrue tspec_SpecTrue_withSpace : core.


Lemma Triple_SpecTrue {sig : finType} {n : nat} {F : Type} (pM : pTM sig^+ F n) P :
  Triple P pM (fun _ => tspec SpecTrue).
Proof. eapply Consequence_post. apply Triple_True. auto. Qed.


Arguments tspec : simpl never.

Hint Extern 4 =>
     lazymatch goal with
     | [H : _ ≃≃ SpecFalse |- _] => exfalso; now eapply tspec_not_SpecFalse in H
     | [H : _ ≃≃ withSpace SpecFalse _ |- _] => exfalso; now eapply tspec_not_SpecFalse_withSpace in H
     end : core.

Goal forall t : tapes sigNat^+ 4,
    t ≃≃ SpecFalse -> 3 = 4.
Proof. auto. Qed.




(* TODO: Move to [TM.Code.CodeTM] *)
Definition appSize {n : nat} : Vector.t (nat->nat) n -> Vector.t nat n -> Vector.t nat n :=
  fun fs s => tabulate (fun i => fs[@i] s[@i]).

Lemma Triple_RemoveSpace (n : nat) (sig : finType) (F : Type) (P : Spec sig n) (M : pTM sig^+ F n) (Q : F -> Spec sig n) (fs : Vector.t (nat->nat) n) :
  (forall s, Triple (tspec (withSpace P s)) M (fun y => tspec (withSpace (Q y) (appSize fs s)))) -> (* Specifications with size will always have this form *)
  Triple (tspec P) M (fun y => tspec (Q y)).
Proof.
  intro HTrip.
  eapply Realise_monotone with (R' := fun tin '(yout, tout) => forall s, tspec (withSpace P s) tin -> tspec (withSpace (Q yout) (appSize fs s)) tout).
  - unfold Triple, Triple_Rel, Realise in *. intros tin k outc HLoop. intros s HP.
    now specialize HTrip with (1 := HLoop) (2 := HP).
  - clear HTrip. intros tin (yout, tout). intros H HP.
    specialize (H (dummy_sizes tin P)). spec_assert H by now apply tspec_tspec_withSpace.
    now apply tspec_withSpace_tspec in H.
Qed.

Lemma TripleT_RemoveSpace (n : nat) (sig : finType) (F : Type) (P : Spec sig n) (k : nat) (M : pTM sig^+ F n) (Q : F -> Spec sig n) (fs : Vector.t (nat->nat) n) :
  (forall s, TripleT (tspec (withSpace P s)) k M (fun y => tspec (withSpace (Q y) (appSize fs s)))) ->
  TripleT (tspec P) k M (fun y => tspec (Q y)).
Proof.
  intros HTrip. split.
  - eapply Triple_RemoveSpace. intros s. apply HTrip.
  - eapply TerminatesIn_monotone with (T' := fun tin k' => tspec P tin /\ k <= k').
    + unfold TripleT, Triple_TRel, TerminatesIn in *. intros tin k' (HP&Hk).
      specialize (HTrip (dummy_sizes tin P)) as (_&HT).
      specialize HT with (tin0 := tin) (k0 := k). spec_assert HT as (conf&HLoop).
      { split. now apply tspec_tspec_withSpace. reflexivity. }
      exists conf. eapply loop_monotone; eauto.
    + unfold Triple_TRel. intros tin k' (HP&Hk). eauto.
Qed.



(** For good reasons, [tspec] will be declared to don't simplify with [cbn]. However, [tspec_single] simplifies with [cbn]. *)
Lemma tspec_solve (sig : Type) (n : nat) (t : tapes (boundary+sig) n) (R : Vector.t (RegSpec sig) n) :
  (forall i, tspec_single R[@i] t[@i]) ->
  tspec (SpecVector R) t.
Proof. refine (fun P => P). Qed.

(** [withSpace] does also not simplify; but [withSpace_single] does. *)
Lemma tspec_space_solve (sig : Type) (n : nat) (t : tapes (boundary+sig) n) (R : Vector.t (RegSpec sig) n) (ss : Vector.t nat n) :
  (forall i, tspec_single (withSpace_single R[@i] ss[@i]) t[@i]) ->
  tspec (withSpace (SpecVector R) ss) t.
Proof. intros. apply tspec_solve. simpl_vector. auto. Qed.

Lemma tspec_ext (sig : finType) (n : nat) (t : tapes (boundary+sig) n) (R R' : Vector.t (RegSpec sig) n) :
  tspec (SpecVector R') t ->
  (forall i, tspec_single R'[@i] t[@i] -> tspec_single R[@i] t[@i]) ->
  tspec (SpecVector R) t.
Proof.
  intros H1 H2. apply tspec_solve.
  intros i; specialize (H1 i); specialize (H2 i); eauto.
Qed.

Lemma tspec_space_ext (sig : finType) (n : nat) (t : tapes (boundary+sig) n) (R R' : Vector.t (RegSpec sig) n)
      (ss ss' : Vector.t nat n) :
  tspec (withSpace (SpecVector R') ss') t ->
  (forall i, tspec_single (withSpace_single R'[@i] ss'[@i]) t[@i] -> tspec_single (withSpace_single R[@i] ss[@i]) t[@i]) ->
  tspec (withSpace (SpecVector R) ss) t.
Proof.
  intros H1 H2. apply tspec_solve.
  intros i; specialize (H1 i); specialize (H2 i).
  simpl_vector in *; cbn. eauto.
Qed.




(** ** Tape Lifting *)


Section Lifting.

  Variable (sig : Type).

  Variable (m n : nat).

  (** [P] is the premise of the lifted machine [M@I]. *)
  Variable (P : @Spec sig n).

  Variable (I : Vector.t (Fin.t n) m). (* [m<=n] *)
  Hypothesis (HI : dupfree I).


  (** We want to extract from [P] the premise [P'] for [M] *)
  Definition Downlift : @Spec sig m :=
    match P with
    | SpecVector v => SpecVector (select I v)
    | SpecFalse => SpecFalse
    end.

  Lemma tape_fulfill_Downlift_select tp :
    tspec P tp ->
    tspec Downlift (select I tp).
  Proof.
    intros H.
    hnf in H. hnf.
    unfold Downlift.
    destruct P as [ vect | ].
    - intros i. unfold Downlift. rewrite !select_nth. apply H.
    - assumption.
  Qed.


  (** Same specification as in [P] on indices not in [I], but as in [Q] for indices in [I] (lifted).  *)
  Definition Frame (Q : @Spec sig m) : @Spec sig n :=
    match P, Q with
    | SpecVector p, SpecVector q => SpecVector (fill I p q)
    | _, _ => SpecFalse
    end. 

End Lifting.


Lemma LiftTapes_Spec (sig : finType) (F : finType) (m n : nat) (I : Vector.t (Fin.t n) m) (P : Spec sig n) (Q : F -> Spec sig m) (pM : pTM sig^+ F m) :
  dupfree I ->
  Triple (tspec (Downlift P I)) pM (fun y => tspec (Q y)) ->
  Triple (tspec P) (pM@I) (fun y => tspec (Frame P I (Q y))).
Proof.
  intros HDup HTrip.
  destruct P as [ v | ]; auto.

  eapply Realise_monotone.
  { apply LiftTapes_Realise. assumption. apply HTrip. }
  {
    intros tin (yout, tout) (H&HInj). cbn -[Downlift] in *. intros HP.
    spec_assert H by now apply tape_fulfill_Downlift_select.

    hnf. destruct (Q yout); eauto.
    intros j. decide (Vector.In j I) as [HD|HD].
    - unfold Frame.
      apply vect_nth_In' in HD as (ij&HD).
      erewrite fill_correct_nth; eauto.
      hnf in H. specialize (H ij).
      now rewrite select_nth, HD in H.
    - unfold Frame. rewrite fill_not_index; eauto.
      specialize (HInj j HD). rewrite HInj. now apply HP.
  }
Qed.


Lemma LiftTapes_Spec_con (sig : finType) (F : finType) (m n : nat) (I : Vector.t (Fin.t n) m) (P : Spec sig n) (Q : F -> Spec sig m) (R : F -> Spec sig n) (pM : pTM sig^+ F m) :
  dupfree I ->
  Triple (tspec (Downlift P I)) pM (fun y => tspec (Q y)) ->
  (forall yout tout, tspec (Frame P I (Q yout)) tout -> tspec (R yout) tout) ->
  Triple (tspec P) (pM@I) (fun y => tspec (R y)).
Proof. eauto using Consequence_post, LiftTapes_Spec. Qed.


(*
(** Version with disregarded labels *)
Lemma LiftTapes_Spec' (sig : finType) (F : Type) (m n : nat) (I : Vector.t (Fin.t n) m) (P : Spec sig n) (Q : Spec sig m) (pM : pTM sig^+ F m) :
  dupfree I ->
  Triple (tspec (Downlift I P)) pM (fun y => tspec Q) ->
  Triple (tspec P) (pM@I) (fun _ => tspec (Frame I P Q)).
Proof. apply LiftTapes_Spec. Qed.
*)


Lemma LiftTapes_SpecT (sig F : finType)(m n : nat) (I : Vector.t (Fin.t n) m) (P : Spec sig n) (k : nat) (Q : F -> Spec sig m) (pM : pTM sig^+ F m) :
  dupfree I ->
  TripleT (tspec (Downlift P I)) k pM (fun y => tspec (Q y)) ->
  TripleT (tspec P) k (pM@I) (fun y => tspec (Frame P I (Q y))).
Proof.
  intros HDup (HTrip&HTrip').
  split.
  - apply LiftTapes_Spec; eauto.
  - eapply TerminatesIn_monotone.
    + apply LiftTapes_Terminates; eauto.
    + intros tin k' (H&H'). split; auto.
      now apply tape_fulfill_Downlift_select.
Qed.


Lemma LiftTapes_SpecT_con (sig : finType) (F : finType) (m n : nat) (I : Vector.t (Fin.t n) m) (P : Spec sig n) (Q : F -> Spec sig m) (R : F -> Spec sig n)
      (k : nat) (pM : pTM sig^+ F m) :
  dupfree I ->
  TripleT (tspec (Downlift P I)) k pM (fun y => tspec (Q y)) ->
  (forall yout tout, tspec (Frame P I (Q yout)) tout -> tspec (R yout) tout) ->
  TripleT (tspec P) k (pM@I) (fun y => tspec (R y)).
Proof. eauto using ConsequenceT_post, LiftTapes_SpecT. Qed.


(** Swap [Downlift] and [withSpace] *)
Lemma Downlift_withSpace (m n : nat) (sig : Type) (P : Spec sig n) (I : Vector.t (Fin.t n) m) (ss : Vector.t nat n) :
  Downlift (withSpace P ss) I = withSpace (Downlift P I) (select I ss).
Proof.
  destruct P; cbn; f_equal.
  eapply VectorSpec.eq_nth_iff; intros ? ? ->.
  simpl_vector. rewrite !select_nth. simpl_vector. reflexivity.
Qed.

Lemma tspec_Downlift_withSpace (m n : nat) (sig : Type) (P : Spec sig n) (I : Vector.t (Fin.t n) m) (ss : Vector.t nat n)
      (t : tapes (boundary+sig) m) :
  t ≃≃ Downlift (withSpace P ss) I ->
  t ≃≃ withSpace (Downlift P I) (select I ss).
Proof. intros H. erewrite <- Downlift_withSpace; eauto. Qed.

Lemma Triple_Downlift_withSpace (m n : nat) (sig : finType) (P : Spec sig n) (I : Vector.t (Fin.t n) m) (ss : Vector.t nat n)
      (F : Type) (M : pTM sig^+ F m) (Q : F -> Assert sig^+ m) :
  Triple (tspec (withSpace (Downlift P I) (select I ss))) M Q ->
  Triple (tspec (Downlift (withSpace P ss) I)) M Q.
Proof.
  intros H. eapply Consequence_pre.
  - apply H.
  - intros t Ht. now rewrite <- Downlift_withSpace.
Qed.

Lemma TripleT_Downlift_withSpace (m n : nat) (sig : finType) (P : Spec sig n) (I : Vector.t (Fin.t n) m) (ss : Vector.t nat n)
      (F : Type) (k : nat) (M : pTM sig^+ F m) (Q : F -> Assert sig^+ m) :
  TripleT (tspec (withSpace (Downlift P I) (select I ss))) k M Q ->
  TripleT (tspec (Downlift (withSpace P ss) I)) k M Q.
Proof.
  intros H. eapply ConsequenceT_pre.
  - apply H.
  - intros t Ht. now rewrite <- Downlift_withSpace.
  - reflexivity.
Qed.


(* TODO: Move into base *)
Instance dec_ex_fin (n : nat) (P : Fin.t n -> Prop) (decP: forall (i : Fin.t n), dec (P i)) : dec (exists (i : Fin.t n), P i).
Proof.
  induction n.
  - right. intros (i&?). destruct_fin i.
  - decide (P Fin0).
    + left. eauto.
    + specialize (IHn (fun i => P (Fin.FS i))). spec_assert IHn as [IH|IH] by eauto.
      * left. destruct IH as (i&IH). exists (Fin.FS i). eauto.
      * right. intros (j&H). pose proof (fin_destruct_S j) as [(j'&->) | ->]; eauto.
Qed.

(** Move [withFrame] out of [Frame] *)
Lemma Frame_withSpace (m n : nat) (sig : Type) (P : Spec sig n) (P' : Spec sig m) (I : Vector.t (Fin.t n) m) (ss : Vector.t nat n) (ss' : Vector.t nat m) :
  dupfree I ->
  Frame (withSpace P ss) I (withSpace P' ss') = withSpace (Frame P I P') (fill I ss ss').
Proof.
  intros Hdup.
  destruct P, P'; cbn in *; f_equal.
  eapply VectorSpec.eq_nth_iff; intros ? i ->.
  simpl_vector.
  decide (exists j, I[@j]=i) as [(j&Hj)|Hj].
  + erewrite !fill_correct_nth by eauto. now simpl_vector.
  + assert (not_index I i).
    { hnf. intros (k&<-) % vect_nth_In'. contradict Hj. eauto. }
    erewrite !fill_not_index by eauto. now simpl_vector.
Qed.

Lemma tspec_Frame_withSpace
      (m n : nat) (sig : Type) (P : Spec sig n) (P' : Spec sig m) (I : Vector.t (Fin.t n) m) (ss : Vector.t nat n) (ss' : Vector.t nat m)
      (t : tapes (boundary+sig) n) :
  t ≃≃ Frame (withSpace P ss) I (withSpace P' ss') ->
  dupfree I ->
  t ≃≃ withSpace (Frame P I P') (fill I ss ss').
Proof. intros H1 H2. erewrite <- Frame_withSpace; eauto. Qed.

Lemma tspec_Frame_withSpace'
      (m n : nat) (sig : Type) (P : Spec sig n) (P' : Spec sig m) (I : Vector.t (Fin.t n) m) (ss : Vector.t nat n) (ss' : Vector.t nat m)
      (t : tapes (boundary+sig) n) :
  dupfree I ->
  t ≃≃ Frame (withSpace P ss) I (withSpace P' ss') ->
  t ≃≃ withSpace (Frame P I P') (fill I ss ss').
Proof. intros H1 H2. erewrite <- Frame_withSpace; eauto. Qed.

Lemma Triple_Frame_withSpace 
      (m n : nat) (sig : finType) (P : Spec sig n) (P' : Spec sig m)(I : Vector.t (Fin.t n) m) (ss : Vector.t nat n) (ss' : Vector.t nat m)
      (F : Type) (M : pTM sig^+ F n) (Q : F -> Assert sig^+ n) :
  dupfree I ->
  Triple (tspec (withSpace (Frame P I P') (fill I ss ss')))    M Q ->
  Triple (tspec (Frame (withSpace P ss) I (withSpace P' ss'))) M Q.
Proof. intros H1 H2. erewrite Frame_withSpace; eauto. Qed.

Lemma TripleT_Frame_withSpace 
      (m n : nat) (sig : finType) (P : Spec sig n) (P' : Spec sig m)(I : Vector.t (Fin.t n) m) (ss : Vector.t nat n) (ss' : Vector.t nat m)
      (F : Type) (k : nat) (M : pTM sig^+ F n) (Q : F -> Assert sig^+ n) :
  dupfree I ->
  TripleT (tspec (withSpace (Frame P I P') (fill I ss ss')))    k M Q ->
  TripleT (tspec (Frame (withSpace P ss) I (withSpace P' ss'))) k M Q.
Proof. intros H1 H2. erewrite Frame_withSpace; eauto. Qed.



(** Versions of [LiftTapes] with space *)

Lemma LiftTapes_Spec_space (sig F : finType) (m n : nat) (I : Vector.t (Fin.t n) m) (P : Spec sig n) (Q : F -> Spec sig m) (pM : pTM sig^+ F m)
     (ss : Vector.t nat n) (ss' : Vector.t nat m) :
  dupfree I ->
  Triple (tspec (withSpace (Downlift P I) (select I ss))) pM (fun y => tspec (withSpace (Q y) ss')) ->
  Triple (tspec (withSpace P ss)) (pM@I) (fun y => tspec (withSpace (Frame P I (Q y)) (fill I ss ss'))).
Proof.
  intros H1 H2. rewrite <- Downlift_withSpace in H2.
  eapply Consequence.
  - eapply LiftTapes_Spec; eauto. apply H2.
  - auto.
  - intros. cbn in *. eapply tspec_Frame_withSpace in H; eauto.
Qed.

Lemma LiftTapes_SpecT_space (sig F : finType) (m n : nat) (I : Vector.t (Fin.t n) m) (P : Spec sig n) (k : nat) (Q : F -> Spec sig m) (pM : pTM sig^+ F m)
     (ss : Vector.t nat n) (ss' : Vector.t nat m) :
  dupfree I ->
  TripleT (tspec (withSpace (Downlift P I) (select I ss))) k pM (fun y => tspec (withSpace (Q y) ss')) ->
  TripleT (tspec (withSpace P ss)) k (pM@I) (fun y => tspec (withSpace (Frame P I (Q y)) (fill I ss ss'))).
Proof.
  intros H1 H2. rewrite <- Downlift_withSpace in H2.
  eapply ConsequenceT.
  - eapply LiftTapes_SpecT; eauto. apply H2.
  - auto.
  - intros. cbn in *. eapply tspec_Frame_withSpace in H; eauto.
  - reflexivity.
Qed.


Lemma LiftTapes_Spec_space_con (sig : finType) (F : finType) (m n : nat) (I : Vector.t (Fin.t n) m)
      (P : Spec sig n) (Q : F -> Spec sig m) (R : F -> Spec sig n) (ss : Vector.t nat n) (ss' : Vector.t nat m) (ss'' : Vector.t nat n)
      (pM : pTM sig^+ F m) :
  dupfree I ->
  Triple (tspec (withSpace (Downlift P I) (select I ss))) pM (fun y => tspec (withSpace (Q y) ss')) ->
  (forall yout tout, tspec (withSpace (Frame P I (Q yout)) (fill I ss ss')) tout -> tspec (withSpace (R yout) ss'') tout) ->
  Triple (tspec (withSpace P ss)) (pM@I) (fun y => tspec (withSpace (R y) ss'')).
Proof.
  intros H1 H2 H3. rewrite <- Downlift_withSpace in H2. 
  eapply Consequence.
  - apply LiftTapes_Spec; eauto. apply H2.
  - eauto.
  - intros. cbn in *. apply tspec_Frame_withSpace in H; eauto.
Qed.

Lemma LiftTapes_SpecT_space_con (sig : finType) (F : finType) (m n : nat) (I : Vector.t (Fin.t n) m)
      (P : Spec sig n) (Q : F -> Spec sig m) (R : F -> Spec sig n) (ss : Vector.t nat n) (ss' : Vector.t nat m) (ss'' : Vector.t nat n)
      (k : nat) (pM : pTM sig^+ F m) :
  dupfree I ->
  TripleT (tspec (withSpace (Downlift P I) (select I ss))) k pM (fun y => tspec (withSpace (Q y) ss')) ->
  (forall yout tout, tspec (withSpace (Frame P I (Q yout)) (fill I ss ss')) tout -> tspec (withSpace (R yout) ss'') tout) ->
  TripleT (tspec (withSpace P ss)) k (pM@I) (fun y => tspec (withSpace (R y) ss'')).
Proof.
  intros H1 H2 H3. rewrite <- Downlift_withSpace in H2. 
  eapply ConsequenceT.
  - apply LiftTapes_SpecT; eauto. apply H2.
  - eauto.
  - intros. cbn in *. apply tspec_Frame_withSpace in H; eauto.
  - reflexivity.
Qed.







(** ** Alphabet Lifting *)

(** Alphabet lifting is easy. We only have to add the retraction to the specification. *)
(** We could also implement this for abstract hoare triples, like in the below rule for [Custom]. *)
Section AlphabetLifting.

  Variable (sig tau : Type).
  Variable (retr : Retract sig tau).

  Definition LiftSpec_single (T : RegSpec sig) : RegSpec tau :=
    match T with
    | Contains r x => Contains (ComposeRetract retr r) x
    | Contains_size r x s => Contains_size (ComposeRetract retr r) x s
    | Void => Void
    | Void_size s => Void_size s
    | Custom p => Custom (fun t => p (surjectTape (Retr_g) (inl UNKNOWN) t))
    end.

  Variable (n : nat).

  Definition LiftSpec (T : Spec sig n) : Spec tau n :=
    match T with
    | SpecVector vect => SpecVector (Vector.map LiftSpec_single vect)
    | SpecFalse => SpecFalse
    end.

  Lemma LiftSpec_surjectTape_tspec_single t T :
    tspec_single (LiftSpec_single T) t ->
    tspec_single T (surjectTape Retr_g (inl UNKNOWN) t).
  Proof. destruct T; cbn in *; intros; simpl_surject; eauto. Qed.

  Lemma LiftSpec_surjectTape_tspec_single' t T :
    tspec_single T (surjectTape Retr_g (inl UNKNOWN) t) ->
    tspec_single (LiftSpec_single T) t.
  Proof. destruct T; cbn in *; intros; simpl_surject; eauto. Qed.

  Lemma LiftSpec_surjectTapes_tspec tin P :
    tin ≃≃ LiftSpec P ->
    surjectTapes Retr_g (inl UNKNOWN) tin ≃≃ P.
  Proof.
    unfold tspec. intros H. destruct P; auto. cbn in *.
    intros i; specialize (H i); cbn.
    simpl_tape in *. now apply LiftSpec_surjectTape_tspec_single.
  Qed.

  Lemma LiftSpec_surjectTapes_tspec' tin P :
    surjectTapes Retr_g (inl UNKNOWN) tin ≃≃ P ->
    tin ≃≃ LiftSpec P.
  Proof.
    unfold tspec. intros H. destruct P; auto. cbn in *.
    intros i; specialize (H i); cbn.
    simpl_tape in *. now apply LiftSpec_surjectTape_tspec_single'.
  Qed.

  
End AlphabetLifting.


Lemma LiftSpec_withSpace_single (sig tau : Type) (I : Retract sig tau) (P : RegSpec sig) (s : nat) :
  LiftSpec_single I (withSpace_single P s) = withSpace_single (LiftSpec_single I P) s.
Proof. destruct P; cbn; eauto. Qed.

Lemma LiftSpec_withSpace (sig tau : Type) (n : nat) (I : Retract sig tau) (P : Spec sig n) (ss : Vector.t nat n) :
  LiftSpec I (withSpace P ss) = withSpace (LiftSpec I P) ss.
Proof.
  destruct P; cbn; f_equal.
  eapply VectorSpec.eq_nth_iff; intros ? ? ->.
  simpl_vector. apply LiftSpec_withSpace_single.
Qed.

Lemma tspec_LiftSpec_withSpace (sig tau : Type) (n : nat) (I : Retract sig tau) (P : Spec sig n) (ss : Vector.t nat n)
      (t : tapes (boundary+tau) n) :
  t ≃≃ LiftSpec I (withSpace P ss) ->
  t ≃≃ withSpace (LiftSpec I P) ss.
Proof. now rewrite LiftSpec_withSpace. Qed.

Lemma tspec_LiftSpec_withSpace' (sig tau : Type) (n : nat) (I : Retract sig tau) (P : Spec sig n) (ss : Vector.t nat n)
      (t : tapes (boundary+tau) n) :
  t ≃≃ withSpace (LiftSpec I P) ss ->
  t ≃≃ LiftSpec I (withSpace P ss).
Proof. now rewrite LiftSpec_withSpace. Qed.

Lemma Triple_LiftSpec_withSpace (sig tau : finType) (n : nat) (I : Retract sig tau) (P : Spec sig n) (ss : Vector.t nat n)
      (F : Type) (M : pTM tau^+ F n) (Q : F -> Assert (boundary+tau) n) :
  Triple (tspec (withSpace (LiftSpec I P) ss)) M Q ->
  Triple (tspec (LiftSpec I (withSpace P ss))) M Q.
Proof. now rewrite LiftSpec_withSpace. Qed.

Lemma TripleT_LiftSpec_withSpace (sig tau : finType) (n : nat) (I : Retract sig tau) (P : Spec sig n) (ss : Vector.t nat n)
      (F : Type) (k : nat) (M : pTM tau^+ F n) (Q : F -> Assert (boundary+tau) n) :
  TripleT (tspec (withSpace (LiftSpec I P) ss)) k M Q ->
  TripleT (tspec (LiftSpec I (withSpace P ss))) k M Q.
Proof. now rewrite LiftSpec_withSpace. Qed.



Section AlphabetLifting'.

  Variable (sig tau : finType) (n : nat).
  Variable (retr : Retract sig tau).
  

  Lemma ChangeAlphabet_Spec(F : finType) (P : Spec sig n) (pM : pTM sig^+ F n) (Q : F -> Spec sig n) :
    Triple (tspec P) pM (fun yout => tspec (Q yout)) ->
    Triple (tspec (LiftSpec retr P)) (ChangeAlphabet pM retr) (fun yout => tspec (LiftSpec retr (Q yout))).
  Proof.
    intros HTrip. eapply Realise_monotone.
    - TM_Correct. eassumption.
    - intros tin (yout, tout) H Henc. cbn in *.
      spec_assert H by now apply LiftSpec_surjectTapes_tspec.
      now apply LiftSpec_surjectTapes_tspec'.
  Qed.

  Lemma ChangeAlphabet_SpecT (F : finType) (P : Spec sig n) (k : nat) (pM : pTM sig^+ F n) (Q : F -> Spec sig n) :
    TripleT (tspec P) k pM (fun yout => tspec (Q yout)) ->
    TripleT (tspec (LiftSpec retr P)) k (ChangeAlphabet pM retr) (fun yout => tspec (LiftSpec retr (Q yout))).
  Proof.
    intros HTrip. split.
    { apply ChangeAlphabet_Spec. eapply TripleT_Triple; eauto. }
    {
      eapply TerminatesIn_monotone.
      - TM_Correct. apply HTrip.
      - unfold Triple_TRel. intros tin k' (H&Hk). cbn. split; auto.
        now apply LiftSpec_surjectTapes_tspec.
    }
  Qed.



  (** We always have to use at least [Consequence_pre], because the premise will never match. *)

  Lemma ChangeAlphabet_Spec_pre_post (F : finType)
        (P : Spec sig n) (P' : Spec tau n)
        (pM : pTM sig^+ F n)
        (Q : F -> Spec sig n) (Q' : F -> Spec tau n) :
    Triple (tspec P) pM (fun yout => tspec (Q yout) ) ->
    (forall t : tapes tau^+ n, t ≃≃ P' -> t ≃≃ LiftSpec retr P) ->
    (forall yout tout, tspec (LiftSpec retr (Q yout)) tout ->  tspec (Q' yout) tout ) ->
    Triple (tspec P') (pM ⇑ retr) (fun yout => tspec (Q' yout)).
  Proof.
    intros H1 H2 H3.
    eapply Consequence.
    - apply ChangeAlphabet_Spec. apply H1.
    - apply H2.
    - apply H3.
  Qed.

  Lemma ChangeAlphabet_SpecT_pre_post (F : finType)
        (P : Spec sig n) (P' : Spec tau n)
        (k : nat) (pM : pTM sig^+ F n)
        (Q : F -> Spec sig n) (Q' : F -> Spec tau n) :
    TripleT (tspec P) k pM (fun yout => tspec (Q yout) ) ->
    (forall t : tapes tau^+ n, t ≃≃ P' -> t ≃≃ LiftSpec retr P) ->
    (forall yout tout, tspec (LiftSpec retr (Q yout)) tout ->  tspec (Q' yout) tout ) ->
    TripleT (tspec P') k (pM ⇑ retr) (fun yout => tspec (Q' yout)).
  Proof.
    intros H1 H2 H3.
    eapply ConsequenceT.
    - apply ChangeAlphabet_SpecT. apply H1.
    - apply H2.
    - apply H3.
    - reflexivity.
  Qed.

  
  Lemma ChangeAlphabet_Spec_pre (F : finType)
        (P : Spec sig n) (P' : Spec tau n)
        (pM : pTM sig^+ F n)
        (Q : F -> Spec sig n) :
    Triple (tspec P) pM (fun yout => tspec (Q yout)) ->
    (forall t : tapes tau^+ n, t ≃≃ P' -> t ≃≃ LiftSpec retr P) ->
    Triple (tspec P') (pM ⇑ retr) (fun yout => tspec (LiftSpec retr (Q yout))).
  Proof.
    intros H1 H2.
    eapply Consequence.
    - apply ChangeAlphabet_Spec. apply H1.
    - apply H2.
    - eauto.
  Qed.

  Lemma ChangeAlphabet_SpecT_pre (F : finType)
        (P : Spec sig n) (P' : Spec tau n)
        (k : nat) (pM : pTM sig^+ F n)
        (Q : F -> Spec sig n) :
    TripleT (tspec P) k pM (fun yout => tspec (Q yout)) ->
    (forall t : tapes tau^+ n, t ≃≃ P' -> t ≃≃ LiftSpec retr P) ->
    TripleT (tspec P') k (pM ⇑ retr) (fun yout => tspec (LiftSpec retr (Q yout))).
  Proof.
    intros H1 H2.
    eapply ConsequenceT.
    - apply ChangeAlphabet_SpecT. apply H1.
    - apply H2.
    - eauto.
    - reflexivity.
  Qed.



  (** Versions with space *)

  Lemma ChangeAlphabet_Spec_space_pre_post (F : finType)
        (P : Spec sig n) (P' : Spec tau n)
        (pM : pTM sig^+ F n)
        (Q : F -> Spec sig n) (Q' : F -> Spec tau n)
        (ss ss' : Vector.t nat n) :
    Triple (tspec (withSpace P ss)) pM (fun yout => tspec (withSpace (Q yout) ss')) ->
    (forall t : tapes tau^+ n, t ≃≃ withSpace P' ss -> t ≃≃ withSpace (LiftSpec retr P) ss) ->
    (forall yout tout, tspec (withSpace (LiftSpec retr (Q yout)) ss') tout ->  tspec (withSpace (Q' yout) ss') tout ) ->
    Triple (tspec (withSpace P' ss)) (pM ⇑ retr) (fun yout => tspec (withSpace (Q' yout) ss')).
  Proof.
    intros H1 H2 H3.
    eapply Consequence.
    - apply ChangeAlphabet_Spec. apply H1.
    - rewrite LiftSpec_withSpace. apply H2.
    - cbn. intros. rewrite LiftSpec_withSpace in H. now apply H3.
  Qed.

  Lemma ChangeAlphabet_SpecT_space_pre_post (F : finType)
        (P : Spec sig n) (P' : Spec tau n)
        (k : nat) (pM : pTM sig^+ F n)
        (Q : F -> Spec sig n) (Q' : F -> Spec tau n)
        (ss ss' : Vector.t nat n) :
    TripleT (tspec (withSpace P ss)) k pM (fun yout => tspec (withSpace (Q yout) ss')) ->
    (forall t : tapes tau^+ n, t ≃≃ withSpace P' ss -> t ≃≃ withSpace (LiftSpec retr P) ss) ->
    (forall yout tout, tspec (withSpace (LiftSpec retr (Q yout)) ss') tout ->  tspec (withSpace (Q' yout) ss') tout ) ->
    TripleT (tspec (withSpace P' ss)) k (pM ⇑ retr) (fun yout => tspec (withSpace (Q' yout) ss')).
  Proof.
    intros H1 H2 H3.
    eapply ConsequenceT.
    - apply ChangeAlphabet_SpecT. apply H1.
    - rewrite LiftSpec_withSpace. apply H2.
    - cbn. intros. rewrite LiftSpec_withSpace in H. now apply H3.
    - reflexivity.
  Qed.

  

  Lemma ChangeAlphabet_Spec_space_pre (F : finType)
        (P : Spec sig n) (P' : Spec tau n)
        (pM : pTM sig^+ F n)
        (Q : F -> Spec sig n)
        (ss ss' : Vector.t nat n) :
    Triple (tspec (withSpace P ss)) pM (fun yout => tspec (withSpace (Q yout) ss')) ->
    (forall t : tapes tau^+ n, t ≃≃ withSpace P' ss -> t ≃≃ withSpace (LiftSpec retr P) ss) ->
    Triple (tspec (withSpace P' ss)) (pM ⇑ retr) (fun yout => tspec (withSpace (LiftSpec retr (Q yout)) ss')).
  Proof.
    intros H1 H2.
    eapply Consequence.
    - apply ChangeAlphabet_Spec. apply H1.
    - rewrite LiftSpec_withSpace. apply H2.
    - cbn. intros. rewrite LiftSpec_withSpace in H. now apply H.
  Qed.

  Lemma ChangeAlphabet_SpecT_space_pre (F : finType)
        (P : Spec sig n) (P' : Spec tau n)
        (k : nat) (pM : pTM sig^+ F n)
        (Q : F -> Spec sig n)
        (ss ss' : Vector.t nat n) :
    TripleT (tspec (withSpace P ss)) k pM (fun yout => tspec (withSpace (Q yout) ss')) ->
    (forall t : tapes tau^+ n, t ≃≃ withSpace P' ss -> t ≃≃ withSpace (LiftSpec retr P) ss) ->
    TripleT (tspec (withSpace P' ss)) k (pM ⇑ retr) (fun yout => tspec (withSpace (LiftSpec retr (Q yout)) ss')).
  Proof.
    intros H1 H2.
    eapply ConsequenceT.
    - apply ChangeAlphabet_SpecT. apply H1.
    - rewrite LiftSpec_withSpace. apply H2.
    - cbn. intros. rewrite LiftSpec_withSpace in H. now apply H.
    - reflexivity.
  Qed.
  
End AlphabetLifting'.


(*
Lemma ChangeAlphabet_Rel (sig tau : finType) (I : Retract sig tau) (n : nat) (F : finType) (M : pTM sig^+ F n) (R : pRel sig^+ F n) (R' : pRel tau^+ F n) :
  M ⊨ R ->
  (forall (tin : tapes tau^+ n) yout tout, R (surjectTapes Retr_g (inl UNKNOWN) tin) (yout, surjectTapes Retr_g (inl UNKNOWN) tout) -> R' tin (yout, tout)) ->
  M ⇑ I ⊨ R'.
Proof.
  intros HRel H.
  eapply Realise_monotone.
  - TM_Correct. apply HRel.
  - intros tin (yout, tout) H'. cbn in *. eauto.
Qed.
*)






(** We always want to keep [withSpace] right after [tspec] in the assertions. *)
Global Arguments withSpace : simpl never.


