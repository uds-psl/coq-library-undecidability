(** ** Hoare Rules for Machines from [Code/] *)

From Undecidability Require Import ProgrammingTools.
From Undecidability Require Import Hoare.HoareLogic Hoare.HoareCombinators Hoare.HoareRegister Hoare.HoareTactics.


(** *** Copy.v *)

From Undecidability Require Import TM.Code.Copy.

(** We give all rule variants here, because automation is forbidden for these machines *)


(* TODO: [CopyValue_size] should be renamed, and this function should be moved to [Code.v] *)
Definition CopyValue_sizefun {sigX X : Type} {cX : codable sigX X} (x : X) : Vector.t (nat->nat) 2 := [|id; CopyValue_size x|].

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
    modpon H. tspec_solve. 
  - intros tin k HEnc. cbn in *.
    specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1.
    cbn in *; simpl_vector in *; cbn in *. eauto.
Qed.

Lemma CopyValue_SpecT (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) :
  TripleT (tspec (SpecVector [|Contains _ x; Void|])) (CopyValue_steps x) (CopyValue _) (fun _ => tspec (SpecVector [|Contains _ x; Contains _ x|])).
Proof. eapply TripleT_RemoveSpace. cbn. intros s. apply CopyValue_SpecT_size. Qed.

Lemma CopyValue_Spec_size (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) (ss : Vector.t nat 2) :
  Triple (tspec (withSpace (SpecVector [|Contains _ x; Void|]) ss))
         (CopyValue _)
         (fun _ => tspec (withSpace (SpecVector [|Contains _ x; Contains _ x|]) (appSize (CopyValue_sizefun x) ss))).
Proof. eapply TripleT_Triple. apply CopyValue_SpecT_size. Qed.

Lemma CopyValue_Spec (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) :
  Triple (tspec (SpecVector [|Contains _ x; Void|]))
         (CopyValue _)
         (fun _ => tspec (SpecVector [|Contains _ x; Contains _ x|])).
Proof. eapply Triple_RemoveSpace. apply CopyValue_Spec_size. Qed.



Lemma Reset_SpecT_space (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) (ss : Vector.t nat 1) :
  TripleT (tspec (withSpace (SpecVector [|Contains _ x|]) ss)) (Reset_steps x) (Reset _) (fun _ => tspec (withSpace (SpecVector [|Void|]) (appSize [|Reset_size x|] ss))).
Proof.
  eapply Realise_TripleT.
  - apply Reset_Realise.
  - apply Reset_Terminates.
  - intros tin [] tout H HEnc. cbn in *.
    specialize (HEnc Fin0); cbn in *. simpl_vector in *; cbn in *.
    modpon H.
    

    tspec_solve.
  - intros tin k HEnc. cbn in *.
    specialize (HEnc Fin0). simpl_vector in *; cbn in *. eauto.
Qed.

Lemma Reset_SpecT (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) :
  TripleT (tspec (SpecVector [|Contains _ x|])) (Reset_steps x) (Reset _) (fun _ => tspec (SpecVector [|Void|])).
Proof. eapply TripleT_RemoveSpace. apply Reset_SpecT_space. Qed.

Lemma Reset_Spec_size (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) ss :
  Triple (tspec (withSpace (SpecVector [|Contains _ x|]) ss)) (Reset _) (fun _ => tspec (withSpace (SpecVector [|Void|]) (appSize [|Reset_size x|] ss))).
Proof. eapply TripleT_Triple. apply Reset_SpecT_space. Qed.

Lemma Reset_Spec (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) :
  Triple (tspec (SpecVector [|Contains _ x|])) (Reset _) (fun _ => tspec (SpecVector [|Void|])).
Proof. eapply TripleT_Triple. apply Reset_SpecT. Qed.


Lemma ResetEmpty_SpecT_space (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) (ss : Vector.t nat 1) :
  cX x = [] ->
  TripleT (tspec (withSpace (SpecVector [|Contains _ x|]) ss)) (ResetEmpty_steps) (ResetEmpty _) (fun _ => tspec (withSpace (SpecVector [|Void|]) (appSize [|ResetEmpty_size|] ss))).
Proof.
  intros HEncEmpty. eapply RealiseIn_TripleT.
  - apply ResetEmpty_Sem.
  - intros tin [] tout H HEnc. cbn in *.
    specialize (HEnc Fin0); cbn in *. simpl_vector in *; cbn in *.
    modpon H. tspec_solve.
Qed.

Lemma ResetEmpty_SpecT (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) :
  cX x = [] ->
  TripleT (tspec (SpecVector [|Contains _ x|])) (ResetEmpty_steps) (ResetEmpty _) (fun _ => tspec (SpecVector [|Void|])).
Proof. intros. eapply TripleT_RemoveSpace. intros. now apply ResetEmpty_SpecT_space. Qed.

Lemma ResetEmpty_Spec_size (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) ss :
  cX x = [] ->
  Triple (tspec (withSpace (SpecVector [|Contains _ x|]) ss)) (ResetEmpty _) (fun _ => tspec (withSpace (SpecVector [|Void|]) (appSize [|ResetEmpty_size|] ss))).
Proof. intros. eapply TripleT_Triple. now apply ResetEmpty_SpecT_space. Qed.

Lemma ResetEmpty_Spec (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) :
  cX x = [] ->
  Triple (tspec (SpecVector [|Contains _ x|])) (ResetEmpty _) (fun _ => tspec (SpecVector [|Void|])).
Proof. intros. eapply TripleT_Triple. now apply ResetEmpty_SpecT. Qed.


Lemma ResetEmpty1_SpecT_space (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) (ss : Vector.t nat 1) :
  size cX x = 1 ->
  TripleT (tspec (withSpace (SpecVector [|Contains _ x|]) ss)) (ResetEmpty1_steps) (ResetEmpty1 _) (fun _ => tspec (withSpace (SpecVector [|Void|]) (appSize [|ResetEmpty1_size|] ss))).
Proof.
  intros HEncEmpty. eapply RealiseIn_TripleT.
  - apply ResetEmpty1_Sem.
  - intros tin [] tout H HEnc. cbn in *.
    specialize (HEnc Fin0); cbn in *. simpl_vector in *; cbn in *.
    modpon H. tspec_solve.
Qed.

Lemma ResetEmpty1_SpecT (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) :
  size cX x = 1 ->
  TripleT (tspec (SpecVector [|Contains _ x|])) (ResetEmpty1_steps) (ResetEmpty1 _) (fun _ => tspec (SpecVector [|Void|])).
Proof. intros. eapply TripleT_RemoveSpace. intros. now apply ResetEmpty1_SpecT_space. Qed.

Lemma ResetEmpty1_Spec_size (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) ss :
  size cX x = 1 ->
  Triple (tspec (withSpace (SpecVector [|Contains _ x|]) ss)) (ResetEmpty1 _) (fun _ => tspec (withSpace (SpecVector [|Void|]) (appSize [|ResetEmpty1_size|] ss))).
Proof. intros. eapply TripleT_Triple. now apply ResetEmpty1_SpecT_space. Qed.

Lemma ResetEmpty1_Spec (sig : finType) (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig) (x : X) :
  size cX x = 1 ->
  Triple (tspec (SpecVector [|Contains _ x|])) (ResetEmpty1 _) (fun _ => tspec (SpecVector [|Void|])).
Proof. intros. eapply TripleT_Triple. now apply ResetEmpty1_SpecT. Qed.



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
    modpon H. tspec_solve.
  - intros tin k HEnc. cbn in *.
    specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1. simpl_vector in *; cbn in *. eauto.
Qed.

Lemma MoveValue_SpecT (sig : finType) (sigX sigY X Y : Type)
      (cX : codable sigX X) (cY : codable sigY Y) (I1 : Retract sigX sig) (I2 : Retract sigY sig) (x : X) (y : Y) :
  TripleT (tspec (SpecVector [|Contains _ x; Contains _ y|])) (MoveValue_steps x y) (MoveValue _) (fun _ => tspec (SpecVector [|Void; Contains _ x|])).
Proof. eapply TripleT_RemoveSpace. apply MoveValue_SpecT_size. Qed.

Lemma MoveValue_Spec_size (sig : finType) (sigX sigY X Y : Type)
      (cX : codable sigX X) (cY : codable sigY Y) (I1 : Retract sigX sig) (I2 : Retract sigY sig) (x : X) (y : Y) (ss : Vector.t nat 2) :
  Triple (tspec (withSpace (SpecVector [|Contains _ x; Contains _ y|]) ss)) (MoveValue _)
         (fun _ => tspec (withSpace (SpecVector [|Void; Contains _ x|]) (appSize (MoveValue_size x y) ss))).
Proof. eapply TripleT_Triple. apply MoveValue_SpecT_size. Qed.

Lemma MoveValue_Spec (sig : finType) (sigX sigY X Y : Type)
      (cX : codable sigX X) (cY : codable sigY Y) (I1 : Retract sigX sig) (I2 : Retract sigY sig) (x : X) (y : Y) :
  Triple (tspec (SpecVector [|Contains _ x; Contains _ y|])) (MoveValue _) (fun _ => tspec (SpecVector [|Void; Contains _ x|])).
Proof. eapply TripleT_Triple. apply MoveValue_SpecT. Qed.


Lemma Translate_SpecT_size (sig : finType) (sigX X : Type)
      (cX : codable sigX X) (I1 I2 : Retract sigX sig) (x : X) (ss : Vector.t nat 1) :
  TripleT (tspec (withSpace (SpecVector [|Contains I1 x|]) ss)) (Translate_steps x) (Translate I1 I2)
          (fun _ => tspec (withSpace (SpecVector [|Contains I2 x|]) (appSize [|id|] ss))).
Proof.
  eapply Realise_TripleT.
  - apply Translate_Realise with (X := X).
  - apply Translate_Terminates with (X := X).
  - intros tin [] tout H HEnc. cbn in *.
    specialize (HEnc Fin0) as HEnc0; simpl_vector in *; cbn in *.
    modpon H. tspec_solve.
  - intros tin k HEnc Hk. cbn in *.
    specialize (HEnc Fin0) as HEnc0. simpl_vector in *; cbn in *. unfold Translate_T. eauto.
Qed.

Lemma Translate_SpecT (sig : finType) (sigX X : Type)
      (cX : codable sigX X) (I1 I2 : Retract sigX sig) (x : X) :
  TripleT (tspec (SpecVector [|Contains I1 x|])) (Translate_steps x) (Translate I1 I2)
          (fun _ => tspec (SpecVector [|Contains I2 x|])).
Proof. eapply TripleT_RemoveSpace. apply Translate_SpecT_size. Qed.

Lemma Translate_Spec_size (sig : finType) (sigX X : Type)
      (cX : codable sigX X) (I1 I2 : Retract sigX sig) (x : X) (ss : Vector.t nat 1) :
  Triple (tspec (withSpace (SpecVector [|Contains I1 x|]) ss)) (Translate I1 I2)
         (fun _ => tspec (withSpace (SpecVector [|Contains I2 x|]) (appSize [|id|] ss))).
Proof. eapply TripleT_Triple. apply Translate_SpecT_size. Qed.

Lemma Translate_Spec (sig : finType) (sigX X : Type)
      (cX : codable sigX X) (I1 I2 : Retract sigX sig) (x : X) :
  Triple (tspec (SpecVector [|Contains I1 x|])) (Translate I1 I2)
         (fun _ => tspec (SpecVector [|Contains I2 x|])).
Proof. eapply TripleT_Triple. apply Translate_SpecT. Qed.


(** We must not add these tactics to the automation! (As in [TM_Correct].) *)


(** *** CompareValue *)

(* TODO: s/CompareValues/CompareValue/g *)

From Undecidability Require Import TM.Code.CompareValue.


(* FIXME: I think we can also use [Triple_and_pre] and embed pure propositions into the postcondition. *)

Section CompareValues.

  Variable (sigX : finType) (X : eqType) (cX : codable sigX X).
  Hypothesis (HInj : forall x y, cX x = cX y -> x = y).

  Lemma CompareValue_SpecT_size (x y : X) (ss : Vector.t nat 2) :
    TripleT (tspec (withSpace (SpecVector [|Contains _ x; Contains _ y|]) ss))
            (CompareValues_steps x y) (CompareValues sigX)
            (fun yout => tspec (withSpace ([if yout then x=y else x<>y],[|Contains _ x; Contains _ y|]) (appSize [|id; id|] ss))).
  Proof.
    eapply Realise_TripleT.
    - now apply CompareValues_Realise.
    - now apply CompareValues_TerminatesIn.
    - intros tin yout tout H HEnc. cbn in *. 
      specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1. cbn in *. 
      cbn in *; simpl_vector in *; cbn in *.
      modpon H. rewrite H. tspec_solve. now decide _.
    - intros tin k HEnc Hk. cbn in *.
      specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1.
      cbn in *; simpl_vector in *; cbn in *.
      unfold CompareValues_T. eauto.
  Qed.

  Lemma CompareValue_SpecT (x y : X) :
    TripleT (tspec (SpecVector [|Contains _ x; Contains _ y|]))
            (CompareValues_steps x y) (CompareValues sigX)
            (fun yout => tspec ([if yout then x=y else x<>y],[|Contains _ x; Contains _ y|])).
  Proof. eapply TripleT_RemoveSpace. cbn. intros s. apply CompareValue_SpecT_size. Qed.

  Lemma CompareValue_Spec_size (x y : X) (ss : Vector.t nat 2) :
    Triple (tspec (withSpace (SpecVector [|Contains _ x; Contains _ y|]) ss))
           (CompareValues sigX)
           (fun yout => tspec (withSpace ([if yout then x=y else x<>y],[|Contains _ x; Contains _ y|]) (appSize [|id; id|] ss))).
  Proof. eapply TripleT_Triple. apply CompareValue_SpecT_size. Qed.

  Lemma CompareValue_Spec (x y : X) :
    Triple (tspec (SpecVector [|Contains _ x; Contains _ y|]))
           (CompareValues sigX)
           (fun yout => tspec ([if yout then x=y else x<>y],[|Contains _ x; Contains _ y|])).
  Proof. eapply Triple_RemoveSpace. apply CompareValue_Spec_size. Qed.

End CompareValues.

(** Again, no automation for this *)

(** *** CaseNat *)

From Undecidability Require Import TM.Code.CaseNat.

(** Here, we only need to register the strongest version; the automation takes care of everything. *)

Lemma Constr_O_SpecT_size (ss : Vector.t nat 1) :
  TripleT (tspec (withSpace (SpecVector [|Void|]) ss)) Constr_O_steps Constr_O (fun _ => tspec (withSpace (SpecVector [|Contains _ 0|]) (appSize [|Constr_O_size|] ss))).
Proof.
  eapply RealiseIn_TripleT.
  - apply Constr_O_Sem.
  - intros tin [] tout H1 H2. cbn in *. specialize (H2 Fin0). simpl_vector in *; cbn in *. modpon H1. tspec_solve.
Qed.

Lemma Constr_S_SpecT_size :
  forall (y : nat) ss,
    TripleT (tspec (withSpace (SpecVector [|Contains _ y|]) ss)) Constr_S_steps Constr_S
            (fun _ => tspec (withSpace (SpecVector [|Contains _ (S y)|]) (appSize [|S|] ss))).
Proof.
  intros y ss.
  eapply RealiseIn_TripleT.
  - apply Constr_S_Sem.
  - intros tin [] tout H HEnc. cbn in *.
    specialize (HEnc Fin0). simpl_vector in *; cbn in *. modpon H. tspec_solve.
Qed.

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
         (withSpace ([if yout then y <> 0 else y = 0],[|Contains _ (pred y)|])
            (appSize (CaseNat_size y) ss))).
Proof.
  eapply RealiseIn_TripleT.
  - apply CaseNat_Sem.
  - intros tin yout tout H HEnc. specialize (HEnc Fin0). simpl_vector in *; cbn in *. modpon H.
    destruct yout, y; cbn in *; auto.
    + tspec_solve. easy.
    + tspec_solve. easy.
Qed.

Ltac hstep_Nat :=
  lazymatch goal with
  | [ |- TripleT ?P ?k Constr_O ?Q ] => eapply Constr_O_SpecT_size
  | [ |- TripleT ?P ?k Constr_S ?Q ] => eapply Constr_S_SpecT_size
  | [ |- TripleT ?P ?k CaseNat ?Q ] => eapply CaseNat_SpecT_size
  end.

Smpl Add hstep_Nat : hstep_smpl.



(** *** CaseBool *)

From Undecidability Require Import TM.Code.CaseBool.


Definition CaseBool_size (_ : bool) : Vector.t (nat->nat) 1 :=
   [|plus 2|].

Lemma CaseBool_SpecT_size (b : bool) (ss : Vector.t nat 1) :
  TripleT
    (tspec (withSpace (SpecVector [|Contains _ b|]) ss))
    CaseBool_steps
    CaseBool
    (fun yout =>
       tspec
         (withSpace
            ([yout = b],[|Void|])
            (appSize (CaseBool_size b) ss))). 
Proof.
  eapply RealiseIn_TripleT.
  - apply CaseBool_Sem.
  - intros tin yout tout H HEnc. specialize (HEnc Fin0). simpl_vector in *; cbn in *. modpon H.
    subst yout. tspec_solve. easy.
Qed.

Ltac hstep_Bool :=
  lazymatch goal with
  | [ |- TripleT ?P ?k CaseBool ?Q ] => eapply CaseBool_SpecT_size
  end.

Smpl Add hstep_Bool : hstep_smpl.


(** *** CaseSum *)

From Undecidability Require Import TM.Code.CaseSum.

Section CaseSum.
  Variable (X Y : Type) (sigX sigY : finType) (codX : codable sigX X) (codY : codable sigY Y).

  Lemma Constr_inl_SpecT_size (x : X) (ss : Vector.t nat 1) :
    TripleT
      (tspec (withSpace (SpecVector [|Contains _ x|]) ss)) Constr_inl_steps (Constr_inl sigX sigY)
      (fun _ => tspec (withSpace (SpecVector [|Contains _ (inl x)|]) (appSize [|pred|] ss))).
  Proof.
    eapply RealiseIn_TripleT.
    - apply Constr_inl_Sem.
    - intros tin [] tout H HEnc. cbn in *.
      specialize (HEnc Fin0). simpl_vector in *; cbn in *. modpon H. tspec_solve.
  Qed.

  Lemma Constr_inr_SpecT_size (y : Y) (ss : Vector.t nat 1) :
    TripleT
      (tspec (withSpace (SpecVector [|Contains _ y|]) ss)) Constr_inr_steps (Constr_inr sigX sigY)
      (fun _ => tspec (withSpace (SpecVector [|Contains _ (inr y)|]) (appSize [|pred|] ss))).
  Proof.
    eapply RealiseIn_TripleT.
    - apply Constr_inr_Sem.
    - intros tin [] tout H HEnc. cbn in *.
      specialize (HEnc Fin0). simpl_vector in *; cbn in *. modpon H. tspec_solve.
  Qed.

  Lemma CaseSum_SpecT_size (s : X+Y) (ss : Vector.t nat 1) :
    TripleT
      (tspec (withSpace (SpecVector [|Contains _ s|]) ss)) (CaseSum_steps) (CaseSum sigX sigY)
      (fun yout => tspec (withSpace
                         ([yout = if s then true else false],
                          match s with inl x => [|Contains _ x|] | inr y =>  [|Contains _ y|] end)
                         (appSize [|S|] ss))).
  Proof.
    eapply RealiseIn_TripleT.
    - apply CaseSum_Sem.
    - intros tin yout tout H HEnc. cbn in *.
      specialize (HEnc Fin0). simpl_vector in *; cbn in *. modpon H.
      destruct yout, s; cbn in *; auto; tspec_solve. all:easy.
  Qed.
  
End CaseSum.


Section CaseOpton.
  
  Variable (X : Type) (sigX : finType) (codX : codable sigX X).

  Lemma Constr_Some_SpecT_size (x : X) (ss : Vector.t nat 1) :
    TripleT
      (tspec (withSpace (SpecVector [|Contains _ x|]) ss)) Constr_Some_steps (Constr_Some sigX)
      (fun _ => tspec (withSpace (SpecVector [|Contains _ (Some x)|]) (appSize [|pred|] ss))).
  Proof.
    eapply RealiseIn_TripleT.
    - apply Constr_Some_Sem.
    - intros tin [] tout H HEnc. cbn in *.
      specialize (HEnc Fin0). simpl_vector in *; cbn in *. modpon H. tspec_solve.
  Qed.

  Lemma Constr_None_SpecT_size (ss : Vector.t nat 1) :
    TripleT
      (tspec (withSpace (SpecVector [|Void|]) ss)) Constr_None_steps (Constr_None sigX)
      (fun _ => tspec (withSpace (SpecVector [|Contains _ None|]) (appSize [|pred|] ss))).
  Proof.
    eapply RealiseIn_TripleT.
    - apply Constr_None_Sem.
    - intros tin [] tout H HEnc. cbn in *.
      specialize (HEnc Fin0). simpl_vector in *; cbn in *. modpon H. tspec_solve.
  Qed.

  Definition CaseOption_size (o : option X) : Vector.t (nat->nat) 1 :=
    match o with
    | None => [|CaseOption_size_None|]
    | Some _ => [|CaseOption_size_Some|]
    end.

  Lemma CaseOption_SpecT_size (o : option X) (ss : Vector.t nat 1) :
    TripleT
      (tspec (withSpace (SpecVector [|Contains _ o|]) ss)) (CaseOption_steps) (CaseOption sigX)
      (fun yout => tspec (withSpace
                         ([yout = match o with None => false | _ => true end ],
                          match o with
                          |  Some x => [|Contains _ x|]
                          |  None  => [|Void|]
                          end)
                         (appSize (CaseOption_size o) ss))).
  Proof.
    eapply RealiseIn_TripleT.
    - apply CaseOption_Sem.
    - intros tin yout tout H HEnc. cbn in *.
      specialize (HEnc Fin0). simpl_vector in *; cbn in *. modpon H.
      destruct yout, o; cbn in *; auto; tspec_solve. all:easy.
  Qed.
  
End CaseOpton.


Ltac hstep_Sum_Option :=
  match goal with
  | [ |- TripleT ?P ?k (Constr_inl _ _) ?Q ] => eapply Constr_inl_SpecT_size
  | [ |- TripleT ?P ?k (Constr_inr _ _) ?Q ] => eapply Constr_inr_SpecT_size
  | [ |- TripleT ?P ?k (CaseSum    _ _) ?Q ] => eapply CaseSum_SpecT_size

  | [ |- TripleT ?P ?k (Constr_Some _)  ?Q ] => eapply Constr_Some_SpecT_size
  | [ |- TripleT ?P ?k (Constr_None _)  ?Q ] => eapply Constr_None_SpecT_size
  | [ |- TripleT ?P ?k (CaseOption  _)  ?Q ] => eapply CaseSum_SpecT_size
  end.

Smpl Add hstep_Sum_Option : hstep_smpl.


(** *** CaseList *)

From Undecidability Require Import TM.Code.CaseList.

Section CaseList.

  Variable (X : Type) (sigX : finType) (codX : codable sigX X).

  Definition Constr_cons_sizefun (x : X) : Vector.t (nat->nat) 2 :=
    [|Constr_cons_size x; id|].

  Lemma Constr_cons_SpecT_size (x : X) (xs : list X) (ss : Vector.t nat 2) :
    TripleT
      (tspec (withSpace (SpecVector [|Contains _ xs; Contains _ x|]) ss)) (Constr_cons_steps x) (Constr_cons sigX)
      (fun _ => tspec (withSpace (SpecVector [|Contains _ (x::xs); Contains _ x|]) (appSize (Constr_cons_sizefun x) ss))).
  Proof.
    eapply Realise_TripleT.
    - apply Constr_cons_Realise.
    - apply Constr_cons_Terminates.
    - intros tin [] tout H HEnc. cbn in *.
      specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1; simpl_vector in *; cbn in *.
      modpon H. tspec_solve.
    - intros tin k HEnc Hk. cbn.
      specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1; simpl_vector in *; cbn in *.
      eauto.
  Qed.

  Lemma Constr_nil_SpecT_size (ss : Vector.t nat 1) :
    TripleT
      (tspec (withSpace (SpecVector [|Void|]) ss)) Constr_nil_steps (Constr_nil sigX)
      (fun _ => tspec (withSpace (SpecVector [|Contains _ nil|]) (appSize [|pred|] ss))).
  Proof.
    eapply RealiseIn_TripleT.
    - apply Constr_nil_Sem.
    - intros tin [] tout H HEnc. cbn in *.
      specialize (HEnc Fin0). simpl_vector in *; cbn in *. modpon H. tspec_solve.
  Qed.

  Definition CaseList_size (xs : list X) : Vector.t (nat->nat) 2 :=
    match xs with
    | nil => [|id;id|]
    | x :: xs => [|CaseList_size0 x; CaseList_size1 x|]
    end.

  Lemma CaseList_SpecT_size (xs : list X) (ss : Vector.t nat 2) :
    TripleT
      (tspec (withSpace (SpecVector [|Contains _ xs; Void|]) ss)) (CaseList_steps xs) (CaseList sigX)
      (fun yout => tspec (withSpace
                         ([yout = match xs with [] => false | _ => true end] ,match xs with
                          |   x::xs' => [|Contains _ xs'; Contains _ x|]
                          |    nil => [|Contains _ xs; Void|]
                          end)
                         (appSize (CaseList_size xs) ss))).
  Proof.
    eapply Realise_TripleT.
    - apply CaseList_Realise.
    - apply CaseList_Terminates.
    - intros tin yout tout H HEnc. cbn in *.
      specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1; simpl_vector in *; cbn in *.
      modpon H. destruct yout, xs; cbn in *; eauto.
      + destruct H as (H1&H2). tspec_solve. easy.
      + destruct H as (H1&H2). tspec_solve. easy.
    - intros tin k HEnc Hk. cbn.
      specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1; simpl_vector in *; cbn in *.
      eauto.
  Qed.
  

End CaseList.


Ltac hstep_List :=
  match goal with
  | [ |- TripleT ?P ?k (Constr_cons _) ?Q ] => eapply Constr_cons_SpecT_size
  | [ |- TripleT ?P ?k (Constr_nil  _) ?Q ] => eapply Constr_nil_SpecT_size
  | [ |- TripleT ?P ?k (CaseList    _) ?Q ] => eapply CaseList_SpecT_size
  end.

Smpl Add hstep_List : hstep_smpl.


(** *** CasePair *)

From Undecidability Require Import TM.Code.CasePair.

Section CasePair.

  Variable (X Y : Type) (sigX sigY : finType) (codX : codable sigX X) (codY : codable sigY Y).

  Definition Constr_pair_sizefun (x : X) : Vector.t (nat->nat) 2 :=
    [|id; Constr_pair_size x|].

  Lemma Constr_pair_SpecT_size (x : X) (y : Y) (ss : Vector.t nat 2) :
    TripleT (tspec (withSpace (SpecVector [|Contains _ x; Contains _ y|]) ss))
            (Constr_pair_steps x) (Constr_pair sigX sigY)
            (fun _ => tspec (withSpace (SpecVector [|Contains _ x; Contains _ (x,y)|])
                                    (appSize (Constr_pair_sizefun x) ss))).
  Proof.
    eapply Realise_TripleT.
    - apply Constr_pair_Realise.
    - apply Constr_pair_Terminates.
    - intros tin [] yout H HEnc.
      specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1. simpl_vector in *; cbn in *. 
      modpon H. simpl_vector in *. tspec_solve.
    - intros tin k HEnc Hk.
      specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1. simpl_vector in *; cbn in *. 
      unfold Constr_pair_T. eauto.
  Qed.

  Definition CasePair_size (p : X*Y) : Vector.t (nat->nat) 2 :=
    [| CasePair_size0 (fst p); CasePair_size1 (fst p) |].

  Lemma CasePair_SpecT_size (p : X*Y) (ss : Vector.t nat 2) :
    TripleT (tspec (withSpace (SpecVector [|Contains _ p; Void|]) ss))
            (CasePair_steps (fst p)) (CasePair sigX sigY)
            (fun _ => tspec (withSpace (SpecVector [|Contains _ (snd p); Contains _ (fst p)|])
                                    (appSize (CasePair_size p) ss))).
  Proof.
    eapply Realise_TripleT.
    - apply CasePair_Realise.
    - apply CasePair_Terminates.
    - intros tin [] tout H HEnc. cbn in *.
      specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1. simpl_vector in *; cbn in *. 
      modpon H. simpl_vector in *. tspec_solve.
    - intros tin k HEnc Hk.
      specialize (HEnc Fin0) as HEnc0; specialize (HEnc Fin1) as HEnc1. simpl_vector in *; cbn in *. 
      unfold CasePair_T. eauto.
  Qed.

End CasePair.


Ltac hstep_Pair :=
  match goal with
  | [ |- TripleT ?P ?k (Constr_pair _ _) ?Q ] => eapply Constr_pair_SpecT_size
  | [ |- TripleT ?P ?k (CasePair    _ _) ?Q ] => eapply CasePair_SpecT_size
  end.

Smpl Add hstep_Pair : hstep_smpl.


(** *** CaseFin *)

From Undecidability Require Import TM.Code.CaseFin.


(* FIXME: I am not sure about this one *)
(* FIXME: [ChangeAlphabet] and [LiftTapes] don't support additional pure propositions, yet. *)
(* TODO: We could write a custom rule for [hstep], like for [Return]. *)
Section CaseFin.

  Variable sig : finType.
  Hypothesis defSig : inhabitedC sig.

  (** A non-standard encoding! *)
  Local Existing Instance Encode_Finite.

  Definition CaseFin_size : Vector.t (nat->nat) 1 := [|S>>S|].

  Lemma CaseFin_SpecT_size (x : sig) (ss : Vector.t nat 1) :
    TripleT (tspec (withSpace (SpecVector [|Contains _ x|]) ss))
            (CaseFin_steps) (CaseFin sig)
            (fun yout tout => tspec (withSpace (SpecVector [|Void|]) (appSize CaseFin_size ss)) tout /\ yout = x).
  Proof.
    eapply RealiseIn_TripleT.
    - apply CaseFin_Sem.
    - intros tin yout tout H HEnc. cbn in *.
      specialize (HEnc Fin0). simpl_vector in *; cbn in *. modpon H. split; auto. tspec_solve.
  Qed.

End CaseFin.

(* TODO: For some reason, there is no constructor. It is just [WriteValue [x]]. *)

Ltac hstep_Fin :=
  match goal with
  | [ |- TripleT ?P ?k (CaseFin _) ?Q ] => eapply CaseFin_SpecT_size
  end.

Smpl Add hstep_Pair : hstep_smpl.



(** *** WriteValue *)

(** [WriteValue] is a bit weird. See my thesis for the reason why. *)
(* FIXME: The reason is obsolete (because there should be at most one encoding for each datatype and alphabet). *)
From Undecidability Require Import TM.Code.WriteValue.

Section WriteValue.

  Variable (sig: finType) (X: Type) (cX: codable sig X).

  Definition WriteValue_sizefun (x : X) : Vector.t (nat->nat) 1 := [| WriteValue_size x |].
  
  Lemma WriteValue_SpecT_size (x : X) (ss : Vector.t nat 1) :
    TripleT (tspec (withSpace (SpecVector [|Void|]) ss))
            (WriteValue_steps (size _ x)) (WriteValue (encode x))
            (fun _ => tspec (withSpace (SpecVector [|Contains _ x|]) (appSize (WriteValue_sizefun x) ss))).
  Proof.
    eapply RealiseIn_TripleT.
    - apply WriteValue_Sem.
    - intros tin yout tout H HEnc. cbn in *.
      specialize (HEnc Fin0). simpl_vector in *; cbn in *. modpon H. tspec_solve.
  Qed.

End WriteValue.

Ltac hstep_WriteValue :=
  match goal with
  | [ |- TripleT ?P ?k (WriteValue _) ?Q ] => eapply WriteValue_SpecT_size
  end.

Smpl Add hstep_WriteValue : hstep_smpl.
