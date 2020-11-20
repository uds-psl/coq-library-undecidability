(** ** Examples *)

From Undecidability Require Import ProgrammingTools.
From Undecidability Require Import Hoare.HoareLogic Hoare.HoareCombinators Hoare.HoareRegister Hoare.HoareTactics Hoare.HoareTacticsView.
From Undecidability Require Import CaseNat.

From Coq Require Import ArithRing. (* for [ring_simplify] *)

Arguments mult : simpl never.
Arguments plus : simpl never.


(* Disable the warnings regarding [Undo]. This is a demonstration file. *)
Set Warnings "-undo-batch-mode,-non-interactive".


(** *** Copy.v *)

From Undecidability Require Import TM.Code.Copy.

Definition CopyValue_sizefun {sigX X : Type} {cX : codable sigX X} (x : X) : Vector.t (nat->nat) 2 := [|id; CopyValue_size x|].

(** This is how we specify partital correctness, time, and space in one lemma *)
Lemma CopyValue_SpecT_size (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X)
(ss : Vector.t nat 2) :
  TripleT (≃≃([],withSpace [|Contains _ x; Void|] ss))
          (CopyValue_steps x) (CopyValue sig)
          (fun _ => ≃≃([],withSpace ([|Contains _ x; Contains _ x|]) (appSize (CopyValue_sizefun x) ss))).
Proof.
  start_TM.
  eapply Realise_TripleT.
  - eapply CopyValue_Realise.
  - eapply CopyValue_Terminates.
  - intros tin [] tout H HEnc. unfold withSpace in HEnc.  cbn in *. 
    specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1. cbn in *. 
    cbn in *; simpl_vector in *; cbn in *.
    modpon H. intros i; destruct_fin i; cbn in *; eauto.
  - intros tin k HEnc. unfold withSpace in HEnc.  cbn in *.
    specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1.
    cbn in *; simpl_vector in *; cbn in *. eauto.
Qed.

(** Recover version without space is easy. Normally, we wouldn't write down this lemma because the automation takes care of everything. (But not for [CopyValue], etc!) *)
Lemma CopyValue_SpecT (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) :
  TripleT (≃≃([],[|Contains _ x; Void|])) (CopyValue_steps x) (CopyValue sig) (fun _ => ≃≃([],[|Contains _ x; Contains _ x|])).
Proof. eapply TripleT_RemoveSpace. cbn. intros s. apply CopyValue_SpecT_size. Qed.


Lemma Reset_SpecT_space (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) (ss : Vector.t nat 1) :
  TripleT (≃≃([],withSpace ([|Contains _ x|]) ss)) (Reset_steps x) (Reset sig) (fun _ => ≃≃([],withSpace ([|Void|]) (appSize [|Reset_size x|] ss))).
Proof.
  start_TM.
  eapply Realise_TripleT.
  - eapply Reset_Realise.
  - eapply Reset_Terminates.
  - intros tin [] tout H HEnc. unfold withSpace in HEnc.  cbn in *.
    specialize (HEnc Fin0); cbn in *. simpl_vector in *; cbn in *.
    modpon H. intros i; destruct_fin i; cbn; eauto.
  - intros tin k HEnc. unfold withSpace in HEnc.  cbn in *.
    specialize (HEnc Fin0). simpl_vector in *; cbn in *. eauto.
Qed.

(** This would also not normally be written down. *)
Lemma Reset_SpecT (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) :
  TripleT (≃≃([],[|Contains _ x|])) (Reset_steps x) (Reset sig) (fun _ => ≃≃([], [|Void|])).
Proof. eapply TripleT_RemoveSpace. apply Reset_SpecT_space. Qed.

(** This would also not normally be written down. *)
Lemma Reset_Spec (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) :
  Triple (≃≃([], [|Contains _ x|])) (Reset sig) (fun _ => ≃≃([], [|Void|])).
Proof. eapply TripleT_Triple. apply Reset_SpecT. Qed.


(** Important: The types ([X] and [Y]) or the retractions ([I1] and [I2]) have to be manually instantiated when using these lemmas. *)
(** (With some "non-standard" encodings, the encodings have to be instantiated, of course.) *)

(* TODO: Move to [Code/Copy.v] *)
Definition MoveValue_size {X Y sigX sigY : Type} {cX : codable sigX X} {cY : codable sigY Y} (x : X) (y : Y) : Vector.t (nat->nat) 2 :=
  [|MoveValue_size_x x; MoveValue_size_y x y|].

Lemma MoveValue_SpecT_size (sig : finType) (sigX sigY X Y : Type)
      (cX : codable sigX X) (cY : codable sigY Y) (I1 : Retract sigX sig) (I2 : Retract sigY sig) (x : X) (y : Y) (ss : Vector.t nat 2) :
  TripleT (≃≃([],  withSpace ( [|Contains _ x; Contains _ y|]) ss)) (MoveValue_steps x y) (MoveValue sig)
          (fun _ => ≃≃([],  withSpace ( [|Void; Contains _ x|]) (appSize (MoveValue_size x y) ss))).
Proof.
  start_TM.
  eapply Realise_TripleT.
  - apply MoveValue_Realise with (X := X) (Y := Y).
  - apply MoveValue_Terminates with (X := X) (Y := Y).
  - intros tin [] tout H HEnc. unfold withSpace in HEnc. cbn in *.
    specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1. simpl_vector in *; cbn in *.
    modpon H. intros i; destruct_fin i; cbn; eauto.
  - intros tin k HEnc. unfold withSpace in HEnc. cbn in *.
    specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1. simpl_vector in *; cbn in *. eauto.
Qed.

Lemma MoveValue_SpecT (sig : finType) (sigX sigY X Y : Type)
      (cX : codable sigX X) (cY : codable sigY Y) (I1 : Retract sigX sig) (I2 : Retract sigY sig) (x : X) (y : Y) :
  TripleT (≃≃([], [|Contains _ x; Contains _ y|])) (MoveValue_steps x y) (MoveValue sig) (fun _ => ≃≃([], [|Void; Contains _ x|])).
Proof. eapply TripleT_RemoveSpace. apply MoveValue_SpecT_size. Qed.

Lemma MoveValue_Spec (sig : finType) (sigX sigY X Y : Type)
      (cX : codable sigX X) (cY : codable sigY Y) (I1 : Retract sigX sig) (I2 : Retract sigY sig) (x : X) (y : Y) :
  Triple (≃≃([], [|Contains _ x; Contains _ y|])) (MoveValue sig) (fun _ => ≃≃([], [|Void; Contains _ x|])).
Proof. eapply TripleT_Triple. apply MoveValue_SpecT. Qed.


(** For the abve reasons, we must not add these tactics to the automation! (As in [TM_Correct].) *)

(** *** Constructors for [nat] *)

(** Pure triple (without register specification language); only for demonstration *)
Lemma Constr_O_SpecT_pure :
  TripleT (fun tin => isVoid tin[@Fin0]) (Constr_O_steps) (Constr_O) (fun _ tout => tout[@Fin0] ≃ 0).
Proof.
  start_TM.
  eapply RealiseIn_TripleT.
  - apply Constr_O_Sem.
  - intros tin [] tout H1 H2. cbn in *. unfold tspec in *. modpon H1. unfold_abbrev. contains_ext.
Qed.

Lemma Constr_O_Spec_pure :
  Triple (fun tin => isVoid tin[@Fin0]) (Constr_O) (fun _ tout => tout[@Fin0] ≃ 0).
Proof. eapply TripleT_Triple. apply Constr_O_SpecT_pure. Qed.

Lemma Constr_S_SpecT_pure (y : nat) :
  TripleT (fun tin => tin[@Fin0] ≃ y) (Constr_S_steps) (Constr_S) (fun _ tout => tout[@Fin0] ≃ S y).
Proof.
  eapply RealiseIn_TripleT.
  - apply Constr_S_Sem.
  - intros tin [] tout H1 H2. cbn in *. unfold tspec in *. modpon H1. contains_ext.
Qed.

Lemma Constr_S_Spec_pure (y : nat) :
  Triple (fun tin => tin[@Fin0] ≃ y) (Constr_S) (fun _ tout => tout[@Fin0] ≃ (S y)).
Proof. eapply TripleT_Triple. apply Constr_S_SpecT_pure. Qed.

(** Expressed using the specification language *)

Lemma Constr_O_SpecT_size (ss : Vector.t nat 1) :
  TripleT (≃≃([],  withSpace ( [|Void|]) ss)) Constr_O_steps Constr_O (fun _ => ≃≃([],  withSpace ( [|Contains _ 0|]) (appSize [|Constr_O_size|] ss))).
Proof.
  start_TM.
  eapply RealiseIn_TripleT.
  - apply Constr_O_Sem.
  - intros tin [] tout H1 H2. unfold withSpace in H2. cbn in *. unfold tspec in *. specialize (H2 Fin0). simpl_vector in *; cbn in *. modpon H1.
    hnf. intros i; destruct_fin i; cbn; eauto.
Qed.

Lemma Constr_O_SpecT :
  TripleT (≃≃([], [|Void|])) Constr_O_steps Constr_O (fun _ => ≃≃([], [|Contains _ 0|])).
Proof. eapply TripleT_RemoveSpace; apply Constr_O_SpecT_size. Qed.

Lemma Constr_O_Spec :
  Triple (≃≃([], [|Void|])) Constr_O (fun _ => ≃≃([], [|Contains _ 0|])).
Proof. eapply TripleT_Triple. apply Constr_O_SpecT. Qed.

Lemma Constr_S_SpecT_size :
  forall (y : nat) ss,
    TripleT (≃≃([],  withSpace ( [|Contains _ y|]) ss)) Constr_S_steps Constr_S
            (fun _ => ≃≃([],  withSpace ( [|Contains _ (S y)|]) (appSize [|S|] ss))).
Proof.
  intros y ss. start_TM.
  eapply RealiseIn_TripleT.
  - apply Constr_S_Sem.
  - intros tin [] tout H HEnc. unfold withSpace in *|-. cbn in *.
    specialize (HEnc Fin0). simpl_vector in *; cbn in *. modpon H.
    hnf. intros i; destruct_fin i; cbn; eauto.
Qed.

Lemma Constr_S_SpecT :
  forall (y : nat), TripleT (≃≃([], [|Contains _ y|])) Constr_S_steps Constr_S (fun _ => ≃≃([], [|Contains _ (S y)|])).
Proof. intros. eapply TripleT_RemoveSpace; apply Constr_S_SpecT_size. Qed.

Lemma Constr_S_Spec :
  forall (y : nat), Triple (≃≃([], [|Contains _ y|])) Constr_S (fun _ => ≃≃([], [|Contains _ (S y)|])).
Proof. intros y. eapply TripleT_Triple. apply Constr_S_SpecT. Qed.


Definition CaseNat_size (n : nat) : Vector.t (nat->nat) 1 :=
  match n with
  | O => [|id|]
  | S n' => [|S|]
  end.

Lemma CaseNat_SpecT_size (y : nat) (ss : Vector.t nat 1) :
  TripleT
    (≃≃([],  withSpace ( [|Contains _ y|]) ss))
    CaseNat_steps
    CaseNat
    (fun yout =>
       tspec  ([if yout then y <> 0 else y = 0],
         (withSpace [|Contains _ (pred y)|] (appSize (CaseNat_size y) ss)))). 
Proof.
  start_TM.
  eapply RealiseIn_TripleT.
  - apply CaseNat_Sem.
  - intros tin yout tout H HEnc. unfold withSpace in *|-. specialize (HEnc Fin0). simpl_vector in *; cbn in *. modpon H.
    destruct yout, y; cbn in *; auto.
    + hnf. split. easy. intros i; destruct_fin i; cbn; eauto.
    + hnf. split. easy.  intros i; destruct_fin i; cbn; eauto.
Qed.

Lemma CaseNat_SpecT (y : nat) :
  TripleT
    (≃≃([], [|Contains _ y|]))
    CaseNat_steps
    CaseNat
    (fun yout =>
       tspec  ([if yout then y <> 0 else y = 0],[|Contains _ (pred y)|])).
Proof. eapply TripleT_RemoveSpace. apply CaseNat_SpecT_size. Qed.

Lemma CaseNat_Spec (y : nat) :
  Triple (≃≃([], [|Contains _ y|]))
         CaseNat
         (fun yout =>
            tspec
            ([if yout then y <> 0 else y = 0],[|Contains _ (pred y)|])).
Proof. eapply TripleT_Triple. apply CaseNat_SpecT. Qed.


(** A combination of the consequence rule and the above correctness lemma. (The automation also takes care of this.) *)
Lemma Constr_S_Spec_con (n : nat) (Q : Assert sigNat^+ 1) :
  (forall tout, ≃≃([], [|Contains _ (S n)|]) tout -> Q tout) ->
  Triple (≃≃([], [|Contains _ n|])) Constr_S (fun _ => Q).
Proof. eauto using Consequence_post, Constr_S_Spec. Qed.



(** Add all [nat] (de)constructor lemmas to the automation. We only have to register the complete correctness lemmas. *)
(** Here we demonstrate how to register specifications to the automation. We only have to register the strongest proven variant, e.g. with time & space.
All other (weaker) variants will be derived by the automation on-the-fly, if needed. *)
Ltac hstep_Nat :=
  lazymatch goal with
  | [ |- TripleT ?P ?k Constr_O ?Q ] => eapply Constr_O_SpecT_size
  (* We only use register-machines. There is no need to have lemmas without register specifications. This was only done here for demonstration purposes. *)
  | [ |- TripleT ?P ?k Constr_S ?Q ] => eapply Constr_S_SpecT_size
  | [ |- TripleT ?P ?k CaseNat ?Q ] => eapply CaseNat_SpecT_size
  end.

Smpl Add hstep_Nat : hstep_Spec.



(** *** A simple example *)

(** Pure example: increment a number twice *)

Definition IncrementTwice_steps := 1 + Constr_S_steps + Constr_S_steps.

Definition IncrementTwice : pTM sigNat^+ unit 1 := Constr_S;; Constr_S.

Lemma IncrementTwice_Spec_pure (y : nat) :
  Triple (fun tin => tin[@Fin0] ≃ y) (IncrementTwice) (fun _ tout => tout[@Fin0] ≃ S (S y)).
Proof.
  start_TM.
  eapply Seq_Spec.
  - apply Constr_S_Spec_pure.
  - cbn. intros _. apply Constr_S_Spec_pure.
Restart.
  start_TM.
  unfold IncrementTwice. (* Because the automation is working syntactically, the definition has first to be unfolded (like in [TM_Correct]). *)
  hsteps. apply Constr_S_Spec_pure.
  cbn. intros _. apply Constr_S_Spec_pure.
Qed.

(** With time! *)
Lemma IncrementTwice_SpecT_pure (y : nat) :
  TripleT (fun tin => tin[@Fin0] ≃ y) (IncrementTwice_steps) (IncrementTwice) (fun _ tout => tout[@Fin0] ≃ S (S y)).
Proof.
  start_TM.
  eapply Seq_SpecT.
  - apply Constr_S_SpecT_pure.
  - cbn. intros _. apply Constr_S_SpecT_pure.
  - reflexivity. (* Easy! *)
Restart.
  start_TM.
  unfold IncrementTwice. hsteps. apply Constr_S_SpecT_pure.
  cbn. intros _. apply Constr_S_SpecT_pure.
  reflexivity.
Qed.



(** Same example, but using the specification language *)

Lemma IncrementTwice_Spec (y : nat) :
  Triple (≃≃([], [|Contains _ y|])) (IncrementTwice) (fun _ => ≃≃([], [|Contains _ (S (S y))|])).
Proof.
  start_TM.
  eapply Seq_Spec.
  - apply Constr_S_Spec.
  - cbn. intros _. apply Constr_S_Spec.
Restart. (* Proof with step-by-step automation and without the user-defined tactic for [Constr_S]. *)
  start_TM.
  unfold IncrementTwice. hstep. apply Constr_S_Spec.
  cbn. intros _.
  apply Constr_S_Spec. (* We can directly use [Constr_S_Spec] here, because the postconditions match syntactically. This usually not the case. *)
Restart.
  start_TM.
  unfold IncrementTwice.
  hsteps_cbn. eauto.
  (* The automation always applies the Consequence rule for user-defined specifications, if the postcondition is not an evar. *)
  (* The version [hstep_cbn] calls [cbn] before each step. [forall (x : unit)] will be automatically removed. *)
  (* Note that [hstep_Spec] automatically converted [Constr_S_SpecT_size] to [Constr_S_Spec]. It can handle all combinations of such weakenings. *)
Qed.

Lemma IncrementTwice_SpecT (y : nat) :
  TripleT (≃≃([], [|Contains _ y|])) (IncrementTwice_steps) (IncrementTwice) (fun _ => ≃≃([], [|Contains _ (S (S y))|])).
Proof.
  start_TM.
  eapply Seq_SpecT.
  - apply Constr_S_SpecT.
  - cbn. intros _. apply Constr_S_SpecT.
  - reflexivity.
Restart.
  start_TM.
  unfold IncrementTwice. hstep. apply Constr_S_SpecT.
  cbn. intros _. apply Constr_S_SpecT. (* We can directly use [Constr_S_Spec'] here, because the postconditions match syntactically. This usually not the case. *)
Restart. (* Full automation! *)
  unfold IncrementTwice. hsteps_cbn.
  eauto. reflexivity. (* This is easy, isn't it? *)
Qed.



(** Example using the specification language and lifting: Increment two numbers *)

Definition Incr2 : pTM sigNat^+ unit 2 :=
  Constr_S@[|Fin0|];; Constr_S@[|Fin1|].

Definition Incr2_steps := 1 + Constr_S_steps + Constr_S_steps.



Lemma Incr2_Spec :
  forall (x y : nat), Triple (≃≃([], [|Contains _ x; Contains _ y|])) Incr2 (fun _ => ≃≃([], [|Contains _ (S x); Contains _ (S y)|])).
Proof.
  intros x y. start_TM.
  eapply Seq_Spec.
  - eapply LiftTapes_Spec.
    + smpl_dupfree.
    + cbn. apply Constr_S_Spec.
  - cbn. intros _. eapply LiftTapes_Spec_con. (* For the last step, we have to use the lifting rule with consequence rule. *)
    + smpl_dupfree.
    + cbn. apply Constr_S_Spec.
    + cbn. auto.
      (* After the last step, we have to prove that our "generated" assertion implies the wanted assertion. *)
      (* The prove is completed with simplification. The HUGE advantage is that we never have to rewrite anything! *)
      (* The proof is faster than using realisation directly. *)
Restart.
  (* The tactics can do this automatically *)
  intros x y. unfold Incr2.
  hsteps_cbn. eauto.
Qed.

Lemma Incr2_SpecT :
  forall (x y : nat), TripleT (≃≃([], [|Contains _ x; Contains _ y|])) Incr2_steps Incr2 (fun _ => ≃≃([], [|Contains _ (S x); Contains _ (S y)|])).
Proof.
  intros x y. start_TM.
  eapply Seq_SpecT.
  - eapply LiftTapes_SpecT.
    + smpl_dupfree.
    + cbn. apply Constr_S_SpecT.
  - intros []. cbn [Frame]. eapply LiftTapes_SpecT_con.
    + smpl_dupfree.
    + cbn. apply Constr_S_SpecT.
    + cbn. auto.
  - reflexivity.  (* <- This is the only difference to the above lemma (without time)! We actually don't need to prove [Incr2_Spec] first. *)
Restart.
  intros x y. unfold Incr2. hsteps_cbn. all:reflexivity.
Qed.




(** More increments *)

Definition Incr3 : pTM sigNat^+ unit 3 :=
  Constr_S@[|Fin0|];; Constr_S@[|Fin1|];; IncrementTwice@[|Fin2|].

Definition Incr3_steps := 2 + Constr_S_steps + Constr_S_steps + IncrementTwice_steps.

Lemma Incr3_Spec :
  forall (x y z : nat), Triple (≃≃([], [|Contains _ x; Contains _ y; Contains _ z|])) Incr3 (fun _ => ≃≃([], [|Contains _ (S x); Contains _ (S y); Contains _ (S (S z))|])).
Proof.



  intros x y z. start_TM.
  eapply Seq_Spec.
  - eapply LiftTapes_Spec.
    + smpl_dupfree.
    + cbn. apply Constr_S_Spec.
  - intros []. cbn [Frame].
    eapply Seq_Spec. (* The second Seq just works as the first one. *)
    + eapply LiftTapes_Spec.
      * smpl_dupfree.
      * cbn. apply Constr_S_Spec.
    + intros []. cbn [Frame].
      eapply LiftTapes_Spec_con. (* We again have to use the lifting rule with the consequence rule here. *)
      * smpl_dupfree.
      * cbn. apply IncrementTwice_Spec.
      * cbn. auto. (* Done! *)
Restart.
  intros x y z. unfold Incr3.
  hsteps_cbn. apply IncrementTwice_Spec. cbn. eauto.
Qed.

(** The same with time! *)
Lemma Incr3_SpecT :
  forall (x y z : nat), TripleT (≃≃([], [|Contains _ x; Contains _ y; Contains _ z|])) (Incr3_steps) Incr3 (fun _ => ≃≃([], [|Contains _ (S x); Contains _ (S y); Contains _ (S (S z))|])).
Proof.
  intros x y z. start_TM.
  eapply Seq_SpecT.
  - eapply LiftTapes_SpecT.
    + smpl_dupfree.
    + cbn. apply Constr_S_SpecT.
  - intros []. cbn [Frame].
    eapply Seq_SpecT.
    + eapply LiftTapes_SpecT.
      * smpl_dupfree.
      * cbn. apply Constr_S_SpecT.
    + intros []. cbn [Frame].
      eapply LiftTapes_SpecT_con.
      * smpl_dupfree.
      * cbn. apply IncrementTwice_SpecT.
      * cbn. auto.
    + reflexivity. (* first difference *)
  - reflexivity. (* second difference *)
Restart.
  intros x y z. unfold Incr3.
  hsteps_cbn. apply IncrementTwice_SpecT. cbn. eauto. reflexivity. reflexivity.
Qed.



(** *** Addition *)


Definition Add_Step : pTM sigNat^+ (option unit) 2 :=
  If (CaseNat @ [|Fin1|])
     (Return (Constr_S @ [|Fin0|]) None)
     (Return Nop (Some tt)).

(*
Definition Add_Step_Rel : pRel sigNat^+ (option unit) 2 :=
  fun tin '(yout, tout) =>
    forall a b sa sb,
      tin [@Fin0] ≃(;sa) a ->
      tin [@Fin1] ≃(;sb) b ->
      match yout, b with
      | Some tt, O => (* break *)
        tout[@Fin0] ≃(;sa) a /\
        tout[@Fin1] ≃(;sb) b
      | None, S b' =>
        tout[@Fin0] ≃(;pred sa) S a /\
        tout[@Fin1] ≃(;S sb) b'
      | _, _ => False
      end.
*)


Definition Add_Step_Post : nat*nat -> option unit -> Assert sigNat^+ 2 :=
  fun '(a,b) =>
  (fun yout =>
     ≃≃(([yout = if b then Some tt else None]
            ,[|Contains _ (match b with 0 => a | _ => S a end);Contains _ (pred b)|]))).

Lemma Add_Step_Spec (a b : nat) :
  Triple (≃≃([], [|Contains _ a; Contains _ b|])) Add_Step
         (Add_Step_Post (a,b)).
Proof.
  start_TM.
  eapply If_Spec.
  - apply LiftTapes_Spec.
    + smpl_dupfree.
    + cbn. eapply CaseNat_Spec.
  - cbn. hintros ?. destruct b as [ | b']; cbn [Frame]. contradiction.
    eapply Return_Spec_con.
    + cbn [Vector.nth Vector.caseS Vector.case0].
      apply LiftTapes_Spec.
      * smpl_dupfree.
      * cbn [Downlift select]. apply Constr_S_Spec.
    + cbn. intros. tspec_ext.
  - cbn. hintros ->.
    eapply Return_Spec_con.
    + cbn [Vector.nth Vector.caseS Vector.case0]. apply Nop_Spec.
    + intros []. tspec_ext.
Qed.

Definition Add_Loop : pTM sigNat^+ unit 2 := While Add_Step.

(*
Definition Add_Loop_Rel : pRel sigNat^+ unit 2 :=
  ignoreParam (
      fun tin tout =>
        forall a b sa sb,
          tin [@Fin0] ≃(;sa) a ->
          tin [@Fin1] ≃(;sb) b ->
          tout[@Fin0] ≃(;sa-b) b + a /\
          tout[@Fin1] ≃(;sb+b) 0
    ).
*)

Lemma Add_Loop_Spec (a b : nat) :
  Triple (≃≃([], [|Contains _ a; Contains _ b|]))
         Add_Loop
         (fun _ => ≃≃([], [|Contains _ (a+b); Contains _ 0|])).
Proof.
  eapply While_SpecReg with
      (P := fun '(a,b) => (_,_))
      (Q := fun '(a,b) y => (_,_)) (* to be instantiated by the first proof obligation *) 
      (R := fun '(a,b) y => (_,_)) (x := (a,b)).
  - intros (x,y). eapply Add_Step_Spec. (* Instantiate correctness of [AddStep] *)
  - intros (x,y);cbn. split.
   +intros []. destruct y; intros [=]. 
    replace (x+0) with x by lia. auto.
   +destruct y;intros [=]. eexists (_,_). split.
    *tspec_ext.
    *cbn. tspec_ext. f_equal. nia.
Qed.
 

(** The same with termination! *)

Definition Add_Step_steps : nat := 9.

Lemma Add_Step_SpecT (a b : nat) :
  TripleT (≃≃([], [|Contains _ a; Contains _ b|]))
          Add_Step_steps
          Add_Step
         (Add_Step_Post (a,b)).
Proof.
(*  
eapply If_SpecT_weak'. 
  - apply LiftTapes_SpecT.
    + smpl_dupfree.
    + cbn. eapply CaseNat_SpecT.
  - cbn. destruct b as [ | b']; cbn [Frame]; eauto.
    eapply Return_SpecT_con.
    + cbn [Vector.nth Vector.caseS Vector.case0].
      apply LiftTapes_SpecT.
      * smpl_dupfree.
      * cbn [Downlift select]. apply Constr_S_SpecT.
    + intros []. auto.
  - cbn. destruct b as [ | b']; cbn [Frame]; eauto.
    eapply Return_SpecT_con.
    + cbn. apply Nop_SpecT_con.
    + intros []. auto.
  - reflexivity.
Restart.
  start_TM.
  unfold Add_Step.
  eapply If_SpecT_weak'.
  - hsteps.
  - destruct b as [ | b']; cbn in *; auto.
    hsteps. cbn. eauto.
  - destruct b as [ | b']; cbn in *; auto.
    hsteps. cbn.
    apply Nop_SpecT_con. cbn. eauto. (* We have to manually use other rule for [Nop] here. *)
  - reflexivity.
Restart. *) (* With [If_SpecT] *)
  (* It is important to do the [destruct] before other steps. So we are a bit carefull here. *)
  (* We also have to instantiate the step number for [M3] to [0] manually, because of a Coq bug. We don't have to do it if it isn't [0]. *)
  start_TM. 
  unfold Add_Step. eapply If_SpecT with (k3 := 0). hsteps. all:cbn beta.
  - destruct b as [ | b']; cbn in *; auto. all:hintros ?. contradiction.
    hsteps. cbn. tspec_ext.
  - destruct b as [ | b']; cbn in *; auto. all:hintros ?. 2:congruence.
    hsteps. cbn. tspec_ext.
  -cbn. intros. destruct yout. reflexivity. unfold CaseNat_steps, Add_Step_steps. lia.
Qed.



(** With space *)



Definition Add_Step_size (a b : nat) : Vector.t (nat->nat) 2 :=
  match b with
  | 0 => [|id; id|]
  | S b' => [|S; S|]
  end.

Lemma Add_Step_SpecT_space (a b : nat) (ss : Vector.t nat 2) :
  TripleT
    (≃≃([],  withSpace ( [|Contains _ a; Contains _ b|]) ss))
    Add_Step_steps
    Add_Step
    (fun yout =>
            ≃≃([yout = if b then Some tt else None]
                   ,withSpace [|Contains _ (match b with 0 => a | _ => S a end);Contains _ (pred b)|]
         (appSize (Add_Step_size a b) ss))).
Proof.
  start_TM.
  unfold Add_Step. eapply If_SpecT with (k3 := 0).
  - hsteps_cbn.
  - cbn. hintros ?.  destruct b as [ | b']; cbn in *. easy. hsteps_cbn; cbn. tspec_ext.
  - cbn. hintros ->. hsteps. cbn. tspec_ext.
  - intros. destruct yout. (* reflexivity. unfold CaseNat_steps, Add_Step_steps. lia. *)
    + reflexivity.
    + unfold CaseNat_steps, Add_Step_steps. lia.
Qed.



Definition Add_Loop_steps b := 9 + 10 * b.


Lemma Add_Loop_SpecT (a b : nat) :
  TripleT (≃≃([], [|Contains _ a; Contains _ b|]))
          (Add_Loop_steps b)
          (Add_Loop)
          (fun _ => ≃≃([], [|Contains _ (a+b); Contains _ 0|])).
Proof.
  (* Unification can instantiate the abstractions for us. *)
  unfold Add_Loop. eapply While_SpecTReg with
     (PRE := fun '(a,b) => (_,_)) (INV := fun '(a,b) y => (_,_)) (POST := fun '(a,b) y => (_,_))
     (f__step := fun '(a,b) => _) (f__loop := fun '(a,b) => _) (x := (a,b)).
    - intros (x,y). eapply Add_Step_SpecT. (* Instantiate correctness of [AddStep] *)
    - intros (x,y);cbn. split.
      + intros []. split. 
       * destruct y as [ | y'];cbn. 2:intros;congruence. tspec_ext. f_equal. nia.
       *unfold Add_Step_steps,Add_Loop_steps. nia.  
      +destruct y as [ | y']; cbn in *; auto. easy. intros _.
        eexists (S x, y') (* or [eexists (_,_)] *); cbn. repeat split.
        * tspec_ext.
        * unfold Add_Step_steps, Add_Loop_steps. lia.
        * tspec_ext. f_equal. nia.
Qed.

Fixpoint Add_Loop_size (a b : nat) : Vector.t (nat->nat) 2 :=
  match b with
  | O => Add_Step_size a b
  | S b' => Add_Step_size a b >>> Add_Loop_size (S a) b'
  end.

Lemma Add_Loop_SpecT_size (a b : nat) (ss : Vector.t nat 2) :
  TripleT
    (≃≃([],  withSpace ( [|Contains _ a; Contains _ b|]) ss))
    (Add_Loop_steps b)
    (Add_Loop)
    (fun _ => tspec
             ([], withSpace [|Contains _ (a+b); Contains _ 0|]
                (appSize (Add_Loop_size a b) ss))).
Proof.
  (** We have to add the space vector to the abstract state *)
  eapply While_SpecTReg with (PRE := fun '(a,b,ss) => (_,_)) (INV := fun '(a,b,ss) y => (_,_)) 
    (POST := fun '(a,b,ss) y => (_,_)) (f__loop := fun '(a,b,ss) => _) (f__step := fun '(a,b,ss) => _) (x := (a,b,ss));
    clear a b ss; intros ((x,y),ss).
    - apply Add_Step_SpecT_space.
    - cbn. split.
      +intros []. split. 2:unfold Add_Step_steps, Add_Loop_steps;lia.
       destruct y as [ | y']; cbn in *. 2:easy. tspec_ext. f_equal. nia.
      +destruct y as [ | y']; cbn in *. easy. intros _.
      eexists (S x, y', _); cbn. repeat split.
      * tspec_ext.
      * unfold Add_Step_steps, Add_Loop_steps. lia.
      * tspec_ext. f_equal. nia.
Qed.


Definition Add : pTM sigNat^+ unit 4 :=
  LiftTapes (CopyValue _) [|Fin1; Fin2|];; (* copy n to a *)
  LiftTapes (CopyValue _) [|Fin0; Fin3|];; (* copy m to b *)
  LiftTapes Add_Loop [|Fin2; Fin3|];; (* Main loop *)
  LiftTapes (Reset _) [|Fin3|]. (* Reset b *)

Definition Add_steps m n := 98 + 12 * n + 22 * m.

Lemma Add_SpecT (a b : nat) :
  TripleT (≃≃([], [|Contains _ a; Contains _ b; Void; Void|]))
          (Add_steps a b)
          Add
          (fun _ => ≃≃([], [|Contains _ a; Contains _ b; Contains _ (a+b); Void|])).
Proof.
  start_TM.
  eapply Seq_SpecT.
  eapply LiftTapes_SpecT. smpl_dupfree. eapply CopyValue_SpecT.
  intros []. cbn.
  eapply Seq_SpecT.
  eapply LiftTapes_SpecT. smpl_dupfree. eapply CopyValue_SpecT.
  intros []. cbn.
  eapply Seq_SpecT.
  apply LiftTapes_SpecT. smpl_dupfree. cbn. apply Add_Loop_SpecT.
  cbn. intros _.
  eapply LiftTapes_SpecT_con. smpl_dupfree. eapply Reset_SpecT.
  cbn. intros _. tspec_ext. f_equal. nia.
  reflexivity. reflexivity.
  unfold CopyValue_steps, Add_Loop_steps, Add_steps, Reset_steps. rewrite !Encode_nat_hasSize. lia.
Restart.
  start_TM.
  unfold Add. hsteps_cbn. now apply Add_Loop_SpecT. now apply Reset_SpecT.
  
  (* The only interesting part of the proof! *)
  replace (a+b) with (b+a) by lia. auto.
  reflexivity. reflexivity.
  unfold CopyValue_steps, Add_Loop_steps, Add_steps, Reset_steps. rewrite !Encode_nat_hasSize. lia.
Qed.


Definition Add_space (a b : nat) : Vector.t (nat->nat) 4 :=
  [|(*0*) id; (*1*) id; (*2*) CopyValue_size b >> Add_Loop_size b a @>Fin0;
      (*3*) CopyValue_size a >> (Add_Loop_size b a @>Fin1) >> Reset_size 0 |].

(*
(* Optional *)
Arguments appSize : simpl never.
*)

Lemma Add_SpecT_space (a b : nat) (ss : Vector.t nat 4) :
  TripleT
    (≃≃([],  withSpace ( [|Contains _ a; Contains _ b; Void; Void|]) ss))
    (Add_steps a b)
    Add
    (fun _ => ≃≃([],  withSpace ( [|Contains _ a; Contains _ b; Contains _ (a+b); Void|])
                            (appSize (Add_space a b) ss))).
Proof. (* The tactic [hstep] takes also takes care of moving [withSpace] to the head symbol of each precondition *)
  start_TM.
  unfold Add.
  hstep. hstep.
  apply CopyValue_SpecT_size.
  cbn. intros _. cbn.
  hstep. cbn. hstep. cbn. apply CopyValue_SpecT_size.
  cbn. intros _. hstep. cbn. hstep. cbn. apply Add_Loop_SpecT_size.
  cbn. intros _. hstep. cbn. apply Reset_SpecT_space.
  cbn. intros _. replace (b+a) with (a+b) by lia. auto.
  reflexivity. reflexivity.
  unfold CopyValue_steps, Reset_steps, Add_Loop_steps, Add_steps. rewrite !Encode_nat_hasSize. lia.
Qed.


(** *** Multiplication *)

Definition Mult_Step : pTM sigNat^+ (option unit) 5 :=
  If (LiftTapes CaseNat [|Fin0|])
     (Return (
          LiftTapes Add [|Fin1; Fin2; Fin3; Fin4|];; (* Add(n, c, c') *)
          LiftTapes (MoveValue _) [|Fin3; Fin2|]
        ) (None)) (* continue *)
     (Return Nop (Some tt)). (* break *)


(* (* For comparison: The correctness relation of [Mult_Step] (with space) *)
Definition Mult_Step_Rel : pRel sigNat^+ (option unit) 5 :=
  fun tin '(yout, tout) =>
    forall (c m' n : nat) (sm sn sc s3 s4 : nat),
      tin[@Fin0] ≃(;sm) m' ->
      tin[@Fin1] ≃(;sn) n ->
      tin[@Fin2] ≃(;sc) c ->
      isVoid_size tin[@Fin3] s3 ->
      isVoid_size tin[@Fin4] s4 ->
      match yout, m' with
      | (Some tt), O => (* return *)
        tout[@Fin0] ≃(;sm) m' /\
        tout[@Fin1] ≃(;sn) n /\
        tout[@Fin2] ≃(;sc) c /\
        isVoid_size tout[@Fin3] s3 /\
        isVoid_size tout[@Fin4] s4
      | None, S m'' => (* continue *)
        tout[@Fin0] ≃(;S sm) m'' /\
        tout[@Fin1] ≃(;sn) n /\
        tout[@Fin2] ≃(;sc-n) n + c /\
        isVoid_size tout[@Fin3] (2 + n + c + Add_space2 n c s3)  /\
        isVoid_size tout[@Fin4] (Add_space3 n s4)
      | _, _ => False
      end.
*)

Definition Mult_Step_Post : nat*nat*nat -> option unit -> Assert sigNat^+ 5 :=
  fun '(m',n,c) =>
  (fun yout =>
     ≃≃([yout = if m' then Some tt else None],
        [|Contains _ (pred m'); Contains _ n; Contains _ ( if m' then c else (n + c)); Void; Void|])).

Definition Mult_Step_steps m' n c :=
  match m' with
  | O => 6
  | _ => 168 + 33 * c + 39 * n
  end.


(** We need the strong version [If_SpecT_strong] here, becaue the running time depends on the path *)
Lemma Mult_Step_SpecT m' n c :
  TripleT
    (≃≃([], [|Contains _ m'; Contains _ n; Contains _ c; Void; Void|]))
    (Mult_Step_steps m' n c)
    (Mult_Step)
    ((Mult_Step_Post) (m',n,c)).
Proof.
  start_TM.
  eapply If_SpecTReg.
  - apply LiftTapes_SpecT. smpl_dupfree. cbn. apply CaseNat_SpecT.
  - cbn. destruct m' as [ | m'']; cbn; auto. all:hintros ?. easy. 
    eapply Return_SpecT_con.
    + eapply Seq_SpecT.
      eapply LiftTapes_SpecT. smpl_dupfree. cbn. apply Add_SpecT.
      cbn. intros []. apply LiftTapes_SpecT. smpl_dupfree. cbn. apply MoveValue_SpecT.
      reflexivity.
    + cbn. tspec_ext.
  - cbn. destruct m' as [ | m'']; cbn; auto. all:hintros ?. 2:easy.
    eapply Return_SpecT_con.
    apply Nop_SpecT. cbn. tspec_ext.
  - cbn. intros b.
    unfold Mult_Step_steps, MoveValue_steps, CaseNat_steps, Add_steps.
    destruct b,m';intros H ;rewrite ?Encode_nat_hasSize. (* Normally, this shouldn't be unfolded here. *)
    all:nia.
Restart.
  eapply If_SpecTReg.
  - hsteps.
  - cbn. hintros Hm.  
    hsteps. apply Add_SpecT. cbn. hsteps. reflexivity. cbn.
    destruct m'. easy. cbn. tspec_ext.
  - cbn. hsteps. hintros ? ->. tspec_ext.
  - cbn. intros b. (* This part is the same *)
  unfold Mult_Step_steps, MoveValue_steps, CaseNat_steps, Add_steps.
  destruct b,m';intros H ;rewrite ?Encode_nat_hasSize. (* Normally, this shouldn't be unfolded here. *)
  all:nia.
Qed.


Definition Mult_Step_space m' n c : Vector.t (nat->nat) 5 :=
  match m' with
  | 0 => [|id; id; id; id; id|]
  | S m'' => [| (*0*) S;
               (*1*) Add_space n c @> Fin0; (* = [id] *)
               (*2*) (Add_space n c @> Fin1) >> MoveValue_size_y (n+c) c;
               (*3*) (Add_space n c @> Fin2) >> MoveValue_size_x (n+c);
               (*4*) (Add_space n c @>Fin3) |]
  end.

Lemma Mult_Step_SpecT_size m' n c ss :
  TripleT
    (≃≃([],  withSpace ( [|Contains _ m'; Contains _ n; Contains _ c; Void; Void|]) ss))
    (Mult_Step_steps m' n c)
    (Mult_Step)
    (fun yout =>
       ≃≃([yout = if m' then Some tt else None],
         withSpace 
         [|Contains _ (pred m'); Contains _ n; Contains _ ( if m' then c else (n + c)); Void; Void|] (appSize (Mult_Step_space m' n c) ss))).
Proof.
  start_TM.
  eapply If_SpecTReg.
  - hsteps.
  - cbn. hintros ?. destruct m' as [ | m'']. contradiction. cbn.
    hsteps. apply Add_SpecT_space. cbn. hsteps. cbn. reflexivity. cbn. tspec_ext.
  - cbn. hintros ->. hsteps. tspec_ext.
  - cbn. destruct m'; intros []. 1,4:easy. 
    all:unfold Mult_Step_steps, MoveValue_steps, CaseNat_steps, Add_steps. 2:rewrite !Encode_nat_hasSize.
    all:lia.
Qed.



Definition Mult_Loop := While Mult_Step.

Fixpoint Mult_Loop_steps m' n c :=
  match m' with
  | O => S (Mult_Step_steps m' n c)
  | S m'' => S (Mult_Step_steps m' n c) + Mult_Loop_steps m'' n (n + c)
  end.


Lemma Mult_Loop_SpecT m' n c :
  TripleT
    (≃≃([], [|Contains _ m'; Contains _ n; Contains _ c; Void; Void|]))
    (Mult_Loop_steps m' n c)
    (Mult_Loop)
    (fun _ => ≃≃([], [|Contains _ 0; Contains _ n; Contains _ (m' * n + c); Void; Void|])).
Proof.
  unfold Mult_Loop.
  eapply While_SpecTReg with (PRE := fun '(m',n,c) => (_,_)) (INV := fun '(m',n,c) y => (_,_)) (POST := fun '(m',n,c) y => (_,_))
       (f__loop := fun '(m,n,c) => _) (f__step := fun '(m,n,c) => _) (x:=(m',n,c)) ; clear m' n c;intros ((m'&n')&c).
  - apply Mult_Step_SpecT.
  - cbn. split.
    + intros y H. destruct m'. 2:easy. split. 2:{ cbn. nia. } tspec_ext.
    + destruct m'. easy. cbn. eexists (_,_,_). split. tspec_ext. split. nia. tspec_ext. f_equal. nia.
Qed.

Fixpoint Mult_Loop_size m' n c :=
  match m' with
  | 0 => Mult_Step_space m' n c (* [id;...;id] *)
  | S m'' => Mult_Step_space m' n c >>> Mult_Loop_size m'' n (n+c)
  end.

Lemma Mult_Loop_SpecT_size m' n c ss :
  TripleT
    (≃≃([],  withSpace ( [|Contains _ m'; Contains _ n; Contains _ c; Void; Void|]) ss))
    (Mult_Loop_steps m' n c)
    (Mult_Loop)
    (fun _ => ≃≃([],withSpace
                    [|Contains _ 0; Contains _ n; Contains _ (m' * n + c); Void; Void|]
                    (appSize (Mult_Loop_size m' n c) ss))).
Proof.
  eapply While_SpecTReg with (PRE := fun '(m',n,c,ss) => (_,_)) (INV := fun '(m',n,c,ss) y => (_,_)) (POST := fun '(m',n,c,ss) y => (_,_))
   (f__loop := fun '(m,n,c,ss) => _) (f__step := fun '(m,n,c,ss) => _) (x := (m',n,c,ss));
    clear m' n c ss; intros (((m',n),c),ss).
  - apply Mult_Step_SpecT_size.
  - cbn. split.
    +intros y Hy. destruct m'. 2:easy. split. 2:cbn;lia. tspec_ext.
    +destruct m'. easy. intros _. eexists (_,_,_,_). repeat split.
      *tspec_ext.
      *cbn;nia.
      *tspec_ext. f_equal. cbn. nia.
Qed.

  
Definition Mult : pTM sigNat^+ unit 6 :=
  LiftTapes (CopyValue _) [|Fin0; Fin5|];; (* m' := m *)
  LiftTapes (Constr_O) [|Fin2|];; (* c := 0 *)
  LiftTapes Mult_Loop [|Fin5; Fin1; Fin2; Fin3; Fin4|];; (* Main loop *)
  LiftTapes (Reset _) [|Fin5|]. (* Reset m'=0 *)


Definition Mult_steps (m n : nat) : nat := 12 * m + Mult_Loop_steps m n 0 + 57.


Lemma Mult_SpecT (m n : nat) :
  TripleT
    (≃≃([], [|Contains _ m; Contains _ n; Void; Void; Void; Void|]))
    (Mult_steps m n)
    (Mult)
    (fun _ => ≃≃([], [|Contains _ m; Contains _ n; Contains _ (m * n); Void; Void; Void|])).
Proof.
  start_TM.
  eapply Seq_SpecT.
  apply LiftTapes_SpecT. smpl_dupfree. apply CopyValue_SpecT.
  cbn. intros _. eapply Seq_SpecT.
  apply LiftTapes_SpecT. smpl_dupfree. apply Constr_O_SpecT.
  cbn. intros _. eapply Seq_SpecT.
  apply LiftTapes_SpecT. smpl_dupfree. apply Mult_Loop_SpecT.
  cbn. intros _.
  eapply LiftTapes_SpecT_con. smpl_dupfree. apply Reset_SpecT.
  cbn. intros _. replace (m * n + 0) with (m * n) by lia. auto.
  reflexivity. reflexivity.
  unfold Mult_steps. ring_simplify. unfold CopyValue_steps, Constr_O_steps, Reset_steps. rewrite !Encode_nat_hasSize. cbn. ring_simplify. reflexivity.
Restart.
  unfold Mult. hsteps_cbn.
  apply Mult_Loop_SpecT. apply Reset_SpecT.
  cbn. replace (m * n + 0) with (m * n) by lia. auto. (* This part is the same. *)
  reflexivity. reflexivity.
  unfold Mult_steps. ring_simplify. unfold CopyValue_steps, Constr_O_steps, Reset_steps. rewrite !Encode_nat_hasSize. cbn. ring_simplify. reflexivity.
Qed.



(** Example for bug-spotting in size functions. *)

Definition Mult_size_bug (m n : nat) : Vector.t (nat->nat) 6 :=
  [|(*0*) id;
    (*1*) Mult_Loop_size m n 0 @> Fin1;
    (*2*) Constr_O_size >> Mult_Loop_size m n 0 @> Fin2;
    (*3*) Mult_Loop_size m n 0 @> Fin3;
    (*4*) Mult_Loop_size m n 0 @> Fin4;
    (*5*) CopyValue_size m >> Mult_Loop_size m n 0 @> Fin4 (* Something wrong here! *)
   |].


Lemma Mult_SpecT_space (m n : nat) (ss : Vector.t nat 6) :
  TripleT
    (≃≃([],  withSpace ( [|Contains _ m; Contains _ n; Void; Void; Void; Void|]) ss))
    (Mult_steps m n)
    (Mult)
    (fun _ => ≃≃([],  withSpace ( [|Contains _ m; Contains _ n; Contains _ (m * n); Void; Void; Void|])
                            (appSize (Mult_size_bug m n) ss))).
Proof.
  start_TM.
  unfold Mult.
  hstep. hstep. cbn. 
  apply CopyValue_SpecT_size.
  cbn. intros _. hsteps.
  cbn. intros _. hstep. cbn. hstep. cbn. apply Mult_Loop_SpecT_size.
  cbn. intros. hstep. cbn. apply Reset_SpecT_space.
  cbn. intros _. replace (m * n + 0) with (m * n) by lia.
  Fail now auto. (** If everything was fine, [auto] would have worked here. We can use [tspec_ext] to find what is wrong. *)
  tspec_ext. (** Oh! I forgot to add [>> Reset_size 0]. And it should also be [Fin0] instead of [Fin0] *)
Abort.


Definition Mult_size (m n : nat) : Vector.t (nat->nat) 6 :=
  [|(*0*) id;
    (*1*) Mult_Loop_size m n 0 @> Fin1;
    (*2*) Constr_O_size >> Mult_Loop_size m n 0 @> Fin2;
    (*3*) Mult_Loop_size m n 0 @> Fin3;
    (*4*) Mult_Loop_size m n 0 @> Fin4;
    (*5*) CopyValue_size m >> Mult_Loop_size m n 0 @> Fin0 >> Reset_size 0
   |].

Lemma Mult_SpecT_space (m n : nat) (ss : Vector.t nat 6) :
  TripleT
    (≃≃([],  withSpace ( [|Contains _ m; Contains _ n; Void; Void; Void; Void|]) ss))
    (Mult_steps m n)
    (Mult)
    (fun _ => ≃≃([],  withSpace ( [|Contains _ m; Contains _ n; Contains _ (m * n); Void; Void; Void|])
                            (appSize (Mult_size m n) ss))).
Proof.
  start_TM.
  unfold Mult.
  hstep. hstep. cbn. 
  apply CopyValue_SpecT_size.
  cbn. intros _. hsteps.
  cbn. intros _. hstep. cbn. hstep. cbn. apply Mult_Loop_SpecT_size.
  cbn. intros. hstep. cbn. apply Reset_SpecT_space.
  cbn. intros t. replace (m * n + 0) with (m * n) by lia. auto. (** Now it is fine! *)

  reflexivity. reflexivity.
  unfold Mult_steps. ring_simplify. unfold CopyValue_steps, Constr_O_steps, Reset_steps. rewrite !Encode_nat_hasSize. cbn. ring_simplify. reflexivity.
Qed.

