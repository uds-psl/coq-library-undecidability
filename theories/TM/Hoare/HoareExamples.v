(** ** Examples *)

From Undecidability Require Import ProgrammingTools.
From Undecidability Require Import Hoare.HoareLogic Hoare.HoareCombinators Hoare.HoareRegister Hoare.HoareTactics.
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
Lemma CopyValue_SpecT_size (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) (ss : Vector.t nat 2) :
  TripleT (tspec (withSpace (SpecVector [|Contains _ x; Void|]) ss))
          (CopyValue_steps x) (CopyValue _)
          (fun _ => tspec (withSpace (SpecVector [|Contains _ x; Contains _ x|]) (appSize (CopyValue_sizefun x) ss))).
Proof.
  eapply Realise_TripleT.
  - apply CopyValue_Realise.
  - apply CopyValue_Terminates.
  - intros tin [] tout H HEnc. cbn in *. 
    specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1. cbn in *. 
    cbn in *; simpl_vector in *; cbn in *.
    modpon H. intros i; destruct_fin i; cbn in *; eauto.
  - intros tin k HEnc. cbn in *.
    specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1.
    cbn in *; simpl_vector in *; cbn in *. eauto.
Qed.

(** Recover version without space is easy. Normally, we wouldn't write down this lemma because the automation takes care of everything. (But not for [CopyValue], etc!) *)
Lemma CopyValue_SpecT (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) :
  TripleT (tspec (SpecVector [|Contains _ x; Void|])) (CopyValue_steps x) (CopyValue _) (fun _ => tspec (SpecVector [|Contains _ x; Contains _ x|])).
Proof. eapply TripleT_RemoveSpace. cbn. intros s. apply CopyValue_SpecT_size. Qed.


Lemma Reset_SpecT_space (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) (ss : Vector.t nat 1) :
  TripleT (tspec (withSpace (SpecVector [|Contains _ x|]) ss)) (Reset_steps x) (Reset _) (fun _ => tspec (withSpace (SpecVector [|Void|]) (appSize [|Reset_size x|] ss))).
Proof.
  eapply Realise_TripleT.
  - apply Reset_Realise.
  - apply Reset_Terminates.
  - intros tin [] tout H HEnc. cbn in *.
    specialize (HEnc Fin0); cbn in *. simpl_vector in *; cbn in *.
    modpon H. intros i; destruct_fin i; cbn; eauto.
  - intros tin k HEnc. cbn in *.
    specialize (HEnc Fin0). simpl_vector in *; cbn in *. eauto.
Qed.

(** This would also not normally be written down. *)
Lemma Reset_SpecT (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) :
  TripleT (tspec (SpecVector [|Contains _ x|])) (Reset_steps x) (Reset _) (fun _ => tspec (SpecVector [|Void|])).
Proof. eapply TripleT_RemoveSpace. apply Reset_SpecT_space. Qed.

(** This would also not normally be written down. *)
Lemma Reset_Spec (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) :
  Triple (tspec (SpecVector [|Contains _ x|])) (Reset _) (fun _ => tspec (SpecVector [|Void|])).
Proof. eapply TripleT_Triple. apply Reset_SpecT. Qed.


(** Important: The types ([X] and [Y]) or the retractions ([I1] and [I2]) have to be manually instantiated when using these lemmas. *)
(** (With some "non-standard" encodings, the encodings have to be instantiated, of course.) *)

(* TODO: Move to [Code/Copy.v] *)
Definition MoveValue_size {X Y sigX sigY : Type} {cX : codable sigX X} {cY : codable sigY Y} (x : X) (y : Y) : Vector.t (nat->nat) 2 :=
  [|MoveValue_size_x x; MoveValue_size_y x y|].

Lemma MoveValue_SpecT_size (sig : finType) (sigX sigY X Y : Type)
      (cX : codable sigX X) (cY : codable sigY Y) (I1 : Retract sigX sig) (I2 : Retract sigY sig) (x : X) (y : Y) (ss : Vector.t nat 2) :
  TripleT (tspec (withSpace (SpecVector [|Contains _ x; Contains _ y|]) ss)) (MoveValue_steps x y) (MoveValue _)
          (fun _ => tspec (withSpace (SpecVector [|Void; Contains _ x|]) (appSize (MoveValue_size x y) ss))).
Proof.
  eapply Realise_TripleT.
  - apply MoveValue_Realise with (X := X) (Y := Y).
  - apply MoveValue_Terminates with (X := X) (Y := Y).
  - intros tin [] tout H HEnc. cbn in *.
    specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1. simpl_vector in *; cbn in *.
    modpon H. intros i; destruct_fin i; cbn; eauto.
  - intros tin k HEnc. cbn in *.
    specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1. simpl_vector in *; cbn in *. eauto.
Qed.

Lemma MoveValue_SpecT (sig : finType) (sigX sigY X Y : Type)
      (cX : codable sigX X) (cY : codable sigY Y) (I1 : Retract sigX sig) (I2 : Retract sigY sig) (x : X) (y : Y) :
  TripleT (tspec (SpecVector [|Contains _ x; Contains _ y|])) (MoveValue_steps x y) (MoveValue _) (fun _ => tspec (SpecVector [|Void; Contains _ x|])).
Proof. eapply TripleT_RemoveSpace. apply MoveValue_SpecT_size. Qed.

Lemma MoveValue_Spec (sig : finType) (sigX sigY X Y : Type)
      (cX : codable sigX X) (cY : codable sigY Y) (I1 : Retract sigX sig) (I2 : Retract sigY sig) (x : X) (y : Y) :
  Triple (tspec (SpecVector [|Contains _ x; Contains _ y|])) (MoveValue _) (fun _ => tspec (SpecVector [|Void; Contains _ x|])).
Proof. eapply TripleT_Triple. apply MoveValue_SpecT. Qed.


(** For the abve reasons, we must not add these tactics to the automation! (As in [TM_Correct].) *)

(** *** Constructors for [nat] *)

(** Pure triple (without register specification language); only for demonstration *)
Lemma Constr_O_SpecT_pure :
  TripleT (fun tin => isVoid tin[@Fin0]) (Constr_O_steps) (Constr_O) (fun _ tout => tout[@Fin0] ≃ 0).
Proof.
  eapply RealiseIn_TripleT.
  - apply Constr_O_Sem.
  - intros tin [] tout H1 H2. cbn in *. unfold tspec in *. modpon H1. contains_ext.
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
  TripleT (tspec (withSpace (SpecVector [|Void|]) ss)) Constr_O_steps Constr_O (fun _ => tspec (withSpace (SpecVector [|Contains _ 0|]) (appSize [|Constr_O_size|] ss))).
Proof.
  eapply RealiseIn_TripleT.
  - apply Constr_O_Sem.
  - intros tin [] tout H1 H2. cbn in *. unfold tspec in *. specialize (H2 Fin0). simpl_vector in *; cbn in *. modpon H1.
    hnf. intros i; destruct_fin i; cbn; eauto.
Qed.

Lemma Constr_O_SpecT :
  TripleT (tspec (SpecVector [|Void|])) Constr_O_steps Constr_O (fun _ => tspec (SpecVector [|Contains _ 0|])).
Proof. eapply TripleT_RemoveSpace; apply Constr_O_SpecT_size. Qed.

Lemma Constr_O_Spec :
  Triple (tspec (SpecVector [|Void|])) Constr_O (fun _ => tspec (SpecVector [|Contains _ 0|])).
Proof. eapply TripleT_Triple. apply Constr_O_SpecT. Qed.

Lemma Constr_S_SpecT_size :
  forall (y : nat) ss,
    TripleT (tspec (withSpace (SpecVector [|Contains _ y|]) ss)) Constr_S_steps Constr_S
            (fun _ => tspec (withSpace (SpecVector [|Contains _ (S y)|]) (appSize [|S|] ss))).
Proof.
  intros y ss.
  eapply RealiseIn_TripleT.
  - apply Constr_S_Sem.
  - intros tin [] tout H HEnc. cbn in *.
    specialize (HEnc Fin0). simpl_vector in *; cbn in *. modpon H.
    hnf. intros i; destruct_fin i; cbn; eauto.
Qed.

Lemma Constr_S_SpecT :
  forall (y : nat), TripleT (tspec (SpecVector [|Contains _ y|])) Constr_S_steps Constr_S (fun _ => tspec (SpecVector [|Contains _ (S y)|])).
Proof. intros. eapply TripleT_RemoveSpace; apply Constr_S_SpecT_size. Qed.

Lemma Constr_S_Spec :
  forall (y : nat), Triple (tspec (SpecVector [|Contains _ y|])) Constr_S (fun _ => tspec (SpecVector [|Contains _ (S y)|])).
Proof. intros y. eapply TripleT_Triple. apply Constr_S_SpecT. Qed.


(** For the deconstructor, we have the same weird [match] as in the Realisation rules. Note, that [tspec] must be the head of the expression.
This is way we had to embed [SpecFalse] as a [Spec]. *)

Definition CaseNat_size (n : nat) : Vector.t (nat->nat) 1 :=
  match n with
  | O => [|id|]
  | S n' => [|S|]
  end.

Lemma CaseNat_SpecT_size (y : nat) (ss : Vector.t nat 1) :
  TripleT
    (tspec (withSpace (SpecVector [|Contains _ y|]) ss))
    CaseNat_steps
    CaseNat
    (fun yout =>
       tspec
         (withSpace
            (match yout, y with
             | true, S y' => SpecVector [|Contains _ y'|]
             | false, 0 => SpecVector [|Contains _ 0|]
             | _, _ => SpecFalse
             end)
            (appSize (CaseNat_size y) ss))). (** Note that we add [withSpac] between the [tspec] and the [match] *)
Proof.
  eapply RealiseIn_TripleT.
  - apply CaseNat_Sem.
  - intros tin yout tout H HEnc. specialize (HEnc Fin0). simpl_vector in *; cbn in *. modpon H.
    destruct yout, y; cbn in *; auto.
    + hnf. intros i; destruct_fin i; cbn; eauto.
    + hnf. intros i; destruct_fin i; cbn; eauto.
Qed.

Lemma CaseNat_SpecT (y : nat) :
  TripleT
    (tspec (SpecVector [|Contains _ y|]))
    CaseNat_steps
    CaseNat
    (fun yout =>
       tspec
         match yout, y with
         | true, S y' => SpecVector [|Contains _ y'|]
         | false, 0 => SpecVector [|Contains _ 0|]
         | _, _ => SpecFalse
         end).
Proof. eapply TripleT_RemoveSpace. apply CaseNat_SpecT_size. Qed.

Lemma CaseNat_Spec (y : nat) :
  Triple (tspec (SpecVector [|Contains _ y|]))
         CaseNat
         (fun yout =>
            tspec
              match yout, y with
              | true, S y' => SpecVector [|Contains _ y'|]
              | false, 0 => SpecVector [|Contains _ 0|]
              | _, _ => SpecFalse
              end).
Proof. eapply TripleT_Triple. apply CaseNat_SpecT. Qed.


(** A combination of the consequence rule and the above correctness lemma. (The automation also takes care of this.) *)
Lemma Constr_S_Spec_con (n : nat) (Q : Assert sigNat^+ 1) :
  (forall tout, tspec (SpecVector [|Contains _ (S n)|]) tout -> Q tout) ->
  Triple (tspec (SpecVector [|Contains _ n|])) Constr_S (fun _ => Q).
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

Smpl Add hstep_Nat : hstep_smpl.



(** *** A simple example *)

(** Pure example: increment a number twice *)

Definition IncrementTwice_steps := 1 + Constr_S_steps + Constr_S_steps.

Definition IncrementTwice : pTM sigNat^+ unit 1 := Constr_S;; Constr_S.

Lemma IncrementTwice_Spec_pure (y : nat) :
  Triple (fun tin => tin[@Fin0] ≃ y) (IncrementTwice) (fun _ tout => tout[@Fin0] ≃ S (S y)).
Proof.
  eapply Seq_Spec.
  - apply Constr_S_Spec_pure.
  - cbn. intros _. apply Constr_S_Spec_pure.
Restart.
  unfold IncrementTwice. (* Because the automation is working syntactically, the definition has first to be unfolded (like in [TM_Correct]). *)
  hsteps. apply Constr_S_Spec_pure.
  cbn. intros _. apply Constr_S_Spec_pure.
Qed.

(** With time! *)
Lemma IncrementTwice_SpecT_pure (y : nat) :
  TripleT (fun tin => tin[@Fin0] ≃ y) (IncrementTwice_steps) (IncrementTwice) (fun _ tout => tout[@Fin0] ≃ S (S y)).
Proof.
  eapply Seq_SpecT.
  - apply Constr_S_SpecT_pure.
  - cbn. intros _. apply Constr_S_SpecT_pure.
  - reflexivity. (* Easy! *)
Restart.
  unfold IncrementTwice. hsteps. apply Constr_S_SpecT_pure.
  cbn. intros _. apply Constr_S_SpecT_pure.
  reflexivity.
Qed.



(** Same example, but using the specification language *)

Lemma IncrementTwice_Spec (y : nat) :
  Triple (tspec (SpecVector [|Contains _ y|])) (IncrementTwice) (fun _ => tspec (SpecVector [|Contains _ (S (S y))|])).
Proof.
  eapply Seq_Spec.
  - apply Constr_S_Spec.
  - cbn. intros _. apply Constr_S_Spec.
Restart. (* Proof with step-by-step automation and without the user-defined tactic for [Constr_S]. *)
  unfold IncrementTwice. hstep. apply Constr_S_Spec.
  cbn. intros _.
  apply Constr_S_Spec. (* We can directly use [Constr_S_Spec] here, because the postconditions match syntactically. This usually not the case. *)
Restart.
  unfold IncrementTwice.
  hsteps_cbn. eauto.
  (* The automation always applies the Consequence rule for user-defined specifications, if the postcondition is not an evar. *)
  (* The version [hstep_cbn] calls [cbn] before each step. [forall (x : unit)] will be automatically removed. *)
  (* Note that [hstep_user] automatically converted [Constr_S_SpecT_size] to [Constr_S_Spec]. It can handle all combinations of such weakenings. *)
Qed.

Lemma IncrementTwice_SpecT (y : nat) :
  TripleT (tspec (SpecVector [|Contains _ y|])) (IncrementTwice_steps) (IncrementTwice) (fun _ => tspec (SpecVector [|Contains _ (S (S y))|])).
Proof.
  eapply Seq_SpecT.
  - apply Constr_S_SpecT.
  - cbn. intros _. apply Constr_S_SpecT.
  - reflexivity.
Restart.
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
  forall (x y : nat), Triple (tspec (SpecVector [|Contains _ x; Contains _ y|])) Incr2 (fun _ => tspec (SpecVector [|Contains _ (S x); Contains _ (S y)|])).
Proof.
  intros x y.
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
  forall (x y : nat), TripleT (tspec (SpecVector [|Contains _ x; Contains _ y|])) Incr2_steps Incr2 (fun _ => tspec (SpecVector [|Contains _ (S x); Contains _ (S y)|])).
Proof.
  intros x y.
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
  intros x y. unfold Incr2. hsteps_cbn. eauto. reflexivity.
Qed.




(** More increments *)

Definition Incr3 : pTM sigNat^+ unit 3 :=
  Constr_S@[|Fin0|];; Constr_S@[|Fin1|];; IncrementTwice@[|Fin2|].

Definition Incr3_steps := 2 + Constr_S_steps + Constr_S_steps + IncrementTwice_steps.

Lemma Incr3_Spec :
  forall (x y z : nat), Triple (tspec (SpecVector [|Contains _ x; Contains _ y; Contains _ z|])) Incr3 (fun _ => tspec (SpecVector [|Contains _ (S x); Contains _ (S y); Contains _ (S (S z))|])).
Proof.
  intros x y z.
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
  forall (x y z : nat), TripleT (tspec (SpecVector [|Contains _ x; Contains _ y; Contains _ z|])) (Incr3_steps) Incr3 (fun _ => tspec (SpecVector [|Contains _ (S x); Contains _ (S y); Contains _ (S (S z))|])).
Proof.
  intros x y z.
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
     tspec
       match yout, b with
       | Some _, 0 => SpecVector [|Contains _ a; Contains _ b|]
       | None, S b' => SpecVector [|Contains _ (S a); Contains _ b'|]
       | _, _ => SpecFalse
       end).

Lemma Add_Step_Spec (a b : nat) :
  Triple (tspec (SpecVector [|Contains _ a; Contains _ b|])) Add_Step
         (Add_Step_Post (a,b)).
Proof.
  eapply If_Spec.
  - apply LiftTapes_Spec.
    + smpl_dupfree.
    + cbn. eapply CaseNat_Spec.
  - cbn. destruct b as [ | b']; cbn [Frame]; eauto.
    eapply Return_Spec_con.
    + cbn [Vector.nth Vector.caseS Vector.case0].
      apply LiftTapes_Spec.
      * smpl_dupfree.
      * cbn [Downlift select]. apply Constr_S_Spec.
    + intros []. auto.
  - cbn. destruct b as [ | b']; cbn [Frame]; eauto.
    eapply Return_Spec_con.
    + cbn [Vector.nth Vector.caseS Vector.case0]. apply Nop_Spec.
    + intros []. auto.
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
  Triple (tspec (SpecVector [|Contains _ a; Contains _ b|]))
         Add_Loop
         (fun _ => tspec (SpecVector [|Contains _ (a+b); Contains _ 0|])).
Proof.
  eapply While_Spec with
      (P := fun '(a,b) => _)
      (* (Q := _) (* to be instantiated by the first proof obligation *) *)
      (R := fun '(a,b) => _) (x := (a,b)).
  - intros (x,y). apply Add_Step_Spec. (* Instantiate correctness of [AddStep] *)
  - intros (x,y) yout tmid tout H. cbn in *. (* Termination case *)
    destruct y as [ | y']; cbn in *; auto.
    intros H1 H3. replace (x+0) with x by omega. auto.
  - intros (x,y) tin tmid H1 H2. cbn in *.
    destruct y as [ | y']; cbn in *; auto.
    eexists (_,_); cbn. split.
    + eauto.
    + intros _ tout. replace (S x + y') with (x + S y') by omega. auto.
Qed.



(** The same with termination! *)

Definition Add_Step_steps : nat := 9.

Lemma Add_Step_SpecT (a b : nat) :
  TripleT (tspec (SpecVector [|Contains _ a; Contains _ b|]))
          Add_Step_steps
          Add_Step
         (Add_Step_Post (a,b)).
Proof.
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
  unfold Add_Step.
  eapply If_SpecT_weak'.
  - hsteps.
  - destruct b as [ | b']; cbn in *; auto.
    hsteps. cbn. eauto.
  - destruct b as [ | b']; cbn in *; auto.
    hsteps. cbn.
    apply Nop_SpecT_con. cbn. eauto. (* We have to manually use other rule for [Nop] here. *)
  - reflexivity.
Restart. (* With [If_SpecT] *)
  (* It is important to do the [destruct] before other steps. So we are a bit carefull here. *)
  (* We also have to instantiate the step number for [M3] to [0] manually, because of a Coq bug. We don't have to do it if it isn't [0]. *)
  unfold Add_Step. eapply If_SpecT with (k3 := 0).
  - hsteps.
  - destruct b as [ | b']; cbn in *; auto.
    hsteps. cbn. eauto.
  - destruct b as [ | b']; cbn in *; auto.
    hsteps. cbn. eauto.
  - intros. destruct yout. reflexivity. unfold CaseNat_steps, Add_Step_steps. omega.
Qed.



(** With space *)



Definition Add_Step_size (a b : nat) : Vector.t (nat->nat) 2 :=
  match b with
  | 0 => [|id; id|]
  | S b' => [|S; S|]
  end.

Lemma Add_Step_SpecT_space (a b : nat) (ss : Vector.t nat 2) :
  TripleT
    (tspec (withSpace (SpecVector [|Contains _ a; Contains _ b|]) ss))
    Add_Step_steps
    Add_Step
    (fun yout =>
       tspec
         (withSpace match yout, b with
                    | Some _, 0 => SpecVector [|Contains _ a; Contains _ b|]
                    | None, S b' => SpecVector [|Contains _ (S a); Contains _ b'|]
                    | _, _ => SpecFalse
                    end
         (appSize (Add_Step_size a b) ss))).
Proof.
  unfold Add_Step. eapply If_SpecT with (k3 := 0).
  - hsteps_cbn.
  - destruct b as [ | b']; cbn in *; auto. hsteps_cbn; cbn. auto.
  - destruct b as [ | b']; cbn in *; auto.
    hsteps. cbn. cbn. eauto.
  - intros. destruct yout. (* reflexivity. unfold CaseNat_steps, Add_Step_steps. omega. *)
    + reflexivity.
    + unfold CaseNat_steps, Add_Step_steps. omega.
Qed.



Definition Add_Loop_steps b := 9 + 10 * b.


Lemma Add_Loop_SpecT (a b : nat) :
  TripleT (tspec (SpecVector [|Contains _ a; Contains _ b|]))
          (Add_Loop_steps b)
          (Add_Loop)
          (fun _ => tspec (SpecVector [|Contains _ (a+b); Contains _ 0|])).
Proof.
  (* Unification can instantiate the abstractions for us. *)
  eapply While_SpecT with (P := fun '(a,b) => _) (R := fun '(a,b) => _) (f := fun '(a,b) => _) (g := fun '(a,b) => _) (x := (a,b)).
    - intros (x,y). apply Add_Step_SpecT. (* Instantiate correctness of [AddStep] *)
    - intros (x,y) yout tout Post. cbn in *.
      destruct y as [ | y']; cbn in *; auto.
      intros H1 H2. replace (x+0) with x by omega. auto.
    - intros (x,y); intros.
      destruct y as [ | y']; cbn in *; auto.
      eexists (S x, y') (* or [eexists (_,_)] *); cbn. repeat split.
      + eauto.
      + unfold Add_Step_steps, Add_Loop_steps. omega.
      + replace (S x + y') with (x + S y') by omega. auto.
Qed.

Fixpoint Add_Loop_size (a b : nat) : Vector.t (nat->nat) 2 :=
  match b with
  | O => Add_Step_size a b
  | S b' => Add_Step_size a b >>> Add_Loop_size (S a) b'
  end.

Opaque Triple TripleT.

Lemma Add_Loop_SpecT_size (a b : nat) (ss : Vector.t nat 2) :
  TripleT
    (tspec (withSpace (SpecVector [|Contains _ a; Contains _ b|]) ss))
    (Add_Loop_steps b)
    (Add_Loop)
    (fun _ => tspec
             (withSpace
                (SpecVector [|Contains _ (a+b); Contains _ 0|])
                (appSize (Add_Loop_size a b) ss))).
Proof.
  (** We have to add the space vector to the abstract state *)
  eapply While_SpecT with (P := fun '(a,b,ss) => _) (Q := fun '(a,b,ss) => _) (R := fun '(a,b,ss) => _) (f := fun '(a,b,ss) => _) (g := fun '(a,b,ss) => _) (x := (a,b,ss));
    clear a b ss; intros ((x,y),ss).
    - apply Add_Step_SpecT_space.
    - intros [] tmid tout H1 H2.
      destruct y as [ | y']; cbn in *; auto.
      replace (x+0) with x by omega. split; eauto.
    - intros tin tmid H1 H2.
      destruct y as [ | y']; cbn in *; auto.
      eexists (S x, y', _); cbn. repeat split.
      + eauto.
      + unfold Add_Step_steps, Add_Loop_steps. omega.
      + replace (S x + y') with (x + S y') by omega. auto.
Qed.


Definition Add : pTM sigNat^+ unit 4 :=
  LiftTapes (CopyValue _) [|Fin1; Fin2|];; (* copy n to a *)
  LiftTapes (CopyValue _) [|Fin0; Fin3|];; (* copy m to b *)
  LiftTapes Add_Loop [|Fin2; Fin3|];; (* Main loop *)
  LiftTapes (Reset _) [|Fin3|]. (* Reset b *)

Definition Add_steps m n := 98 + 12 * n + 22 * m.

Lemma Add_SpecT (a b : nat) :
  TripleT (tspec (SpecVector [|Contains _ a; Contains _ b; Void; Void|]))
          (Add_steps a b)
          Add
          (fun _ => tspec (SpecVector [|Contains _ a; Contains _ b; Contains _ (a+b); Void|])).
Proof.
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
  cbn. intros _ tout. replace (a+b) with (b+a) by omega. auto.
  reflexivity. reflexivity.
  unfold CopyValue_steps, Add_Loop_steps, Add_steps, Reset_steps. rewrite !Encode_nat_hasSize. omega.
Restart.
  unfold Add. hsteps_cbn. eapply CopyValue_SpecT. apply CopyValue_SpecT. apply Add_Loop_SpecT. cbn. apply Reset_SpecT. cbn.
  (* The only interesting part of the proof! *)
  replace (a+b) with (b+a) by omega. auto.
  reflexivity. reflexivity.
  unfold CopyValue_steps, Add_Loop_steps, Add_steps, Reset_steps. rewrite !Encode_nat_hasSize. omega.
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
    (tspec (withSpace (SpecVector [|Contains _ a; Contains _ b; Void; Void|]) ss))
    (Add_steps a b)
    Add
    (fun _ => tspec (withSpace (SpecVector [|Contains _ a; Contains _ b; Contains _ (a+b); Void|])
                            (appSize (Add_space a b) ss))).
Proof. (* The tactic [hstep] takes also takes care of moving [withSpace] to the head symbol of each precondition *)
  unfold Add.
  hstep. hstep.
  apply CopyValue_SpecT_size.
  cbn. intros _. cbn.
  hstep. cbn. hstep. cbn. apply CopyValue_SpecT_size.
  cbn. intros _. hstep. cbn. hstep. cbn. apply Add_Loop_SpecT_size.
  cbn. intros _. hstep. cbn. apply Reset_SpecT_space.
  cbn. intros _. replace (b+a) with (a+b) by omega. auto.
  reflexivity. reflexivity.
  unfold CopyValue_steps, Reset_steps, Add_Loop_steps, Add_steps. rewrite !Encode_nat_hasSize. omega.
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
     tspec
       match yout, m' with
       | Some _, 0 => SpecVector [|Contains _ m'; Contains _ n; Contains _ c; Void; Void|]
       | None, S m'' => SpecVector [|Contains _ m''; Contains _ n; Contains _ (n+c); Void; Void|]
       | _, _ => SpecFalse
       end).

Definition Mult_Step_steps m' n c :=
  match m' with
  | O => 6
  | _ => 168 + 33 * c + 39 * n
  end.


(** We need the strong version [If_SpecT_strong] here, becaue the running time depends on the path *)
Lemma Mult_Step_SpecT m' n c :
  TripleT
    (tspec (SpecVector [|Contains _ m'; Contains _ n; Contains _ c; Void; Void|]))
    (Mult_Step_steps m' n c)
    (Mult_Step)
    ((Mult_Step_Post) (m',n,c)).
Proof.
  eapply If_SpecT.
  - apply LiftTapes_SpecT. smpl_dupfree. cbn. apply CaseNat_SpecT.
  - destruct m' as [ | m'']; cbn; auto.
    eapply Return_SpecT_con.
    + eapply Seq_SpecT.
      eapply LiftTapes_SpecT. smpl_dupfree. cbn. apply Add_SpecT.
      cbn. intros []. apply LiftTapes_SpecT. smpl_dupfree. cbn. apply MoveValue_SpecT.
      reflexivity.
    + cbn. auto.
  - destruct m' as [ | m'']; cbn; auto.
    eapply Return_SpecT_con.
    apply Nop_SpecT. cbn. auto.
  - intros tin ymid tout HEnc H1.
    cbn. destruct ymid, m' as [ | m'']; cbn in *; auto.
    unfold Mult_Step_steps, MoveValue_steps, CaseNat_steps, Add_steps. rewrite !Encode_nat_hasSize. (* Normally, this shouldn't be unfolded here. *)
    omega.
Restart.
  eapply If_SpecT.
  - hsteps.
  - destruct m' as [ | m'']; cbn; auto.
    hsteps. apply Add_SpecT. cbn. hsteps. cbn. apply MoveValue_SpecT. reflexivity. cbn. auto.
  - destruct m' as [ | m'']; cbn; auto.
    hsteps. auto.
  - intros tin ymid tout HEnc H1. (* This part is the same *)
    cbn. destruct ymid, m' as [ | m'']; cbn in *; auto.
    unfold Mult_Step_steps, MoveValue_steps, CaseNat_steps, Add_steps. rewrite !Encode_nat_hasSize.
    omega.
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
    (tspec (withSpace (SpecVector [|Contains _ m'; Contains _ n; Contains _ c; Void; Void|]) ss))
    (Mult_Step_steps m' n c)
    (Mult_Step)
    (fun yout =>
       tspec
         (withSpace
            match yout, m' with
            | Some _, 0 => SpecVector [|Contains _ m'; Contains _ n; Contains _ c; Void; Void|]
            | None, S m'' => SpecVector [|Contains _ m''; Contains _ n; Contains _ (n+c); Void; Void|]
            | _, _ => SpecFalse
            end (appSize (Mult_Step_space m' n c) ss))).
Proof.
  eapply If_SpecT.
  - hsteps.
  - destruct m' as [ | m'']; cbn; auto.
    hsteps. apply Add_SpecT_space. cbn. hsteps. cbn. apply MoveValue_SpecT_size. reflexivity. cbn. auto.
  - destruct m' as [ | m'']; cbn; auto.
    hsteps. auto.
  - intros tin ymid tout HEnc H1. (* This part is the same *)
    cbn. destruct ymid, m' as [ | m'']; cbn in *; eauto.
    unfold Mult_Step_steps, MoveValue_steps, CaseNat_steps, Add_steps. rewrite !Encode_nat_hasSize.
    omega.
Qed.



Definition Mult_Loop := While Mult_Step.

Fixpoint Mult_Loop_steps m' n c :=
  match m' with
  | O => S (Mult_Step_steps m' n c)
  | S m'' => S (Mult_Step_steps m' n c) + Mult_Loop_steps m'' n (n + c)
  end.


Lemma Mult_Loop_SpecT m' n c :
  TripleT
    (tspec (SpecVector [|Contains _ m'; Contains _ n; Contains _ c; Void; Void|]))
    (Mult_Loop_steps m' n c)
    (Mult_Loop)
    (fun _ => tspec (SpecVector [|Contains _ 0; Contains _ n; Contains _ (m' * n + c); Void; Void|])).
Proof.
  eapply While_SpecT with (P := fun '(m',n,c) => _) (R := fun '(m',n,c) => _) (f := fun '(m,n,c) => _) (g := fun '(m,n,c) => _) (x := (m',n,c)); clear m' n c.
  - intros ((m'&n)&c). apply Mult_Step_SpecT.
  - intros ((m'&n)&c). cbn. intros _ tmid tout H1 H2. destruct m' as [ | m'']; cbn in *; auto.
  - intros ((m'&n)&c). cbn. intros tin tmid H1 H2. destruct m' as [ | m'']; cbn in *; auto.
    eexists (_,_,_). repeat split; eauto.
    intros _ tout. replace (m'' * n + (n + c)) with (S m'' * n + c) by (ring_simplify; omega). auto.
Qed.

Fixpoint Mult_Loop_size m' n c :=
  match m' with
  | 0 => Mult_Step_space m' n c (* [id;...;id] *)
  | S m'' => Mult_Step_space m' n c >>> Mult_Loop_size m'' n (n+c)
  end.

Lemma Mult_Loop_SpecT_size m' n c ss :
  TripleT
    (tspec (withSpace (SpecVector [|Contains _ m'; Contains _ n; Contains _ c; Void; Void|]) ss))
    (Mult_Loop_steps m' n c)
    (Mult_Loop)
    (fun _ => tspec (withSpace
                    (SpecVector [|Contains _ 0; Contains _ n; Contains _ (m' * n + c); Void; Void|])
                    (appSize (Mult_Loop_size m' n c) ss))).
Proof.
  eapply While_SpecT with (P := fun '(m',n,c,ss) => _) (Q := fun '(m',n,c,ss) => _) (R := fun '(m',n,c,ss) => _) (f := fun '(m,n,c,ss) => _) (g := fun '(m,n,c,ss) => _) (x := (m',n,c,ss));
    clear m' n c ss; intros (((m',n),c),ss).
  - apply Mult_Step_SpecT_size.
  - cbn. intros _ tmid tout H1 H2. destruct m' as [ | m'']; cbn in *; auto.
  - cbn. intros tin tmid H1 H2. destruct m' as [ | m'']; cbn in *; auto.
    eexists (_,_,_,_). repeat split; eauto.
    intros _ tout. replace (m'' * n + (n + c)) with (S m'' * n + c) by (ring_simplify; omega). auto.
Qed.

  
Definition Mult : pTM sigNat^+ unit 6 :=
  LiftTapes (CopyValue _) [|Fin0; Fin5|];; (* m' := m *)
  LiftTapes (Constr_O) [|Fin2|];; (* c := 0 *)
  LiftTapes Mult_Loop [|Fin5; Fin1; Fin2; Fin3; Fin4|];; (* Main loop *)
  LiftTapes (Reset _) [|Fin5|]. (* Reset m'=0 *)


Definition Mult_steps (m n : nat) : nat := 12 * m + Mult_Loop_steps m n 0 + 57.


Lemma Mult_SpecT (m n : nat) :
  TripleT
    (tspec (SpecVector [|Contains _ m; Contains _ n; Void; Void; Void; Void|]))
    (Mult_steps m n)
    (Mult)
    (fun _ => tspec (SpecVector [|Contains _ m; Contains _ n; Contains _ (m * n); Void; Void; Void|])).
Proof.
  eapply Seq_SpecT.
  apply LiftTapes_SpecT. smpl_dupfree. apply CopyValue_SpecT.
  cbn. intros _. eapply Seq_SpecT.
  apply LiftTapes_SpecT. smpl_dupfree. apply Constr_O_SpecT.
  cbn. intros _. eapply Seq_SpecT.
  apply LiftTapes_SpecT. smpl_dupfree. apply Mult_Loop_SpecT.
  cbn. intros _.
  eapply LiftTapes_SpecT_con. smpl_dupfree. apply Reset_SpecT.
  cbn. intros _. replace (m * n + 0) with (m * n) by omega. auto.
  reflexivity. reflexivity.
  unfold Mult_steps. ring_simplify. unfold CopyValue_steps, Constr_O_steps, Reset_steps. rewrite !Encode_nat_hasSize. cbn. ring_simplify. reflexivity.
Restart.
  unfold Mult. hsteps_cbn.
  apply CopyValue_SpecT. hsteps_cbn.
  apply Mult_Loop_SpecT. apply Reset_SpecT.
  cbn. replace (m * n + 0) with (m * n) by omega. auto. (* This part is the same. *)
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
    (tspec (withSpace (SpecVector [|Contains _ m; Contains _ n; Void; Void; Void; Void|]) ss))
    (Mult_steps m n)
    (Mult)
    (fun _ => tspec (withSpace (SpecVector [|Contains _ m; Contains _ n; Contains _ (m * n); Void; Void; Void|])
                            (appSize (Mult_size_bug m n) ss))).
Proof.
  unfold Mult.
  hstep. hstep. cbn. 
  apply CopyValue_SpecT_size.
  cbn. intros _. hsteps.
  cbn. intros _. hstep. cbn. hstep. cbn. apply Mult_Loop_SpecT_size.
  cbn. intros. hstep. cbn. apply Reset_SpecT_space.
  cbn. intros _. replace (m * n + 0) with (m * n) by omega.
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
    (tspec (withSpace (SpecVector [|Contains _ m; Contains _ n; Void; Void; Void; Void|]) ss))
    (Mult_steps m n)
    (Mult)
    (fun _ => tspec (withSpace (SpecVector [|Contains _ m; Contains _ n; Contains _ (m * n); Void; Void; Void|])
                            (appSize (Mult_size m n) ss))).
Proof.
  unfold Mult.
  hstep. hstep. cbn. 
  apply CopyValue_SpecT_size.
  cbn. intros _. hsteps.
  cbn. intros _. hstep. cbn. hstep. cbn. apply Mult_Loop_SpecT_size.
  cbn. intros. hstep. cbn. apply Reset_SpecT_space.
  cbn. intros _ t. replace (m * n + 0) with (m * n) by omega. auto. (** Now it is fine! *)

  reflexivity. reflexivity.
  unfold Mult_steps. ring_simplify. unfold CopyValue_steps, Constr_O_steps, Reset_steps. rewrite !Encode_nat_hasSize. cbn. ring_simplify. reflexivity.
Qed.


(* TODO:
- Examples using the Sigma-lift
*)
