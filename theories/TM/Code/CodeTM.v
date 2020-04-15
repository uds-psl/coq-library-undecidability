From Undecidability Require Export TM.Prelim TM.TM TM.Code.Code.
From Undecidability Require Export TM.Lifting.Lifting.
From Undecidability Require Export TM.Combinators.Combinators.

(** * Value-Containing *)


(** ** Right tapes *)

(** Tape proposition that says that the pointer is on (but not off) the right-most symbol *)
Section IsRight.

  Definition isRight (sig : Type) (t : tape sig) :=
    exists x rs, t = midtape rs x nil.

   Definition isRight_size (sig : Type) (t : tape sig) (s : nat) :=
    exists x rs, t = midtape rs x nil /\ |rs| <= s.


   Lemma isRight_size_isRight (sig : Type) (t : tape sig) (s : nat) :
     isRight_size t s -> isRight t.
   Proof. intros (x&rs&->&_). hnf. eauto. Qed.

  Lemma isRight_size_monotone (sig : Type) (t : tape sig) (s1 s2 : nat) :
    isRight_size t s1 -> s1 <= s2 -> isRight_size t s2.
  Proof. intros (x&rs&->&Hr) Hs. exists x, rs. split. eauto. omega. Qed.

  
  Lemma mapTape_isRight_size (sig tau : Type) (t : tape sig) (s : nat) (f : sig -> tau) :
    isRight_size (mapTape f t) s <-> isRight_size t s.
  Proof.
    split.
    - intros (r1&r2&H&Hs). destruct t; cbn in *; inv H. rewrite map_length in Hs.
      apply map_eq_nil in H3 as ->. hnf. eauto.
    - intros (r1&r2&->&Hs). hnf. cbn. do 2 eexists; repeat split; eauto. now simpl_list.
  Qed.

  Lemma mapTape_isRight (sig tau : Type) (t : tape sig) (f : sig -> tau) :
    isRight (mapTape f t) <-> isRight t.
  Proof.
    split.
    - intros (r1&r2&H). destruct t; cbn in *; inv H.
      apply map_eq_nil in H3 as ->. hnf. eauto.
    - intros (r1&r2&->). hnf. cbn. eauto.
  Qed.

  Lemma isRight_right (sig : Type) (t : tape sig) :
    isRight t -> right t = nil.
  Proof. now intros (x&rs&->). Qed.

  Lemma isRight_size_right (sig : Type) (t : tape sig) (s1 : nat) :
    isRight_size t s1 -> right t = nil.
  Proof. eauto using isRight_right, isRight_size_isRight. Qed.

  Lemma isRight_size_left (sig : Type) (t : tape sig) (s1 : nat) :
    isRight_size t s1 -> length (left t) <= s1.
  Proof. now intros (x&r1&->&H1). Qed.

  Lemma isRight_isRight_size (sig : Type) (t : tape sig) :
    isRight t -> isRight_size t (| tape_local_l t|).
  Proof. intros (x&r2&->). cbn. hnf. eauto. Qed.

  Lemma isRight_size_sizeOfTape (sig : Type) (t : tape sig) (s : nat) :
    isRight_size t s ->
    sizeOfTape t <= 1 + s.
  Proof. intros [m (r1&->&H)]. cbn. simpl_list; cbn. omega. Qed.

End IsRight.

Ltac isRight_mono :=
  lazymatch goal with
  | [ H : isRight_size ?t ?s1 |- isRight_size ?t ?s2 ] =>
    apply isRight_size_monotone with (1 := H); eauto; simpl_comp; try omega
  | [ H : isRight_size ?t ?s1 |- isRight ?t ] =>
    apply isRight_size_isRight with (1 := H)
  | [ H : isRight ?t |- isRight_size ?t ?s2 ] =>
    eapply isRight_size_monotone;
    [ apply (isRight_isRight_size H) | eauto; simpl_comp; try omega ]
  | [ H : isRight ?t |- isRight ?t ] =>
    apply H
  end.
Hint Extern 10 => isRight_mono : core.



(** We add these three symbols the alphabets of every machine. [START] is the first symbol of the encoding and [END] is always the right-most symbol. [UNKNOWN] is always ignored (it is needed for the alphabet-lift). *)
Inductive boundary : Type :=
| START   : boundary
| STOP    : boundary
| UNKNOWN : boundary.

(** Declare discreteness of [boundary] *)
Instance boundary_eq : eq_dec boundary.
Proof. unfold dec. decide equality. Defined.

(** Declare finiteness of [boundary] *)
Instance boundary_fin : finTypeC (EqType boundary).
Proof. split with (enum := [START; STOP; UNKNOWN]). cbn. intros []; cbn; reflexivity. Defined.


(** In this section, we define value-containment (≃). It is defined on tapes over arbitrary [Type]s (even infinite types), not [finType]. *)
Section Fix_Sig.

  Variable (sig : Type).

  Notation "sig '^+'" := ((boundary + sig) % type) (at level 0) : type_scope.


  (** A tape [t] contains a value [x], if [t=midtape rs (inl START) (map inr (encode x) ++ [inl STOP])] for some [rs : list (sig^+)]. This means, the pointer is on the start symbol, right to the pointer is the encoding of [x], which is terminated by the stop symbol [inl STOP]. We write [t ≃ x] for tape [t] contains [x]. *)

  (** We also define a dual predicate for value-containment: reversed value containment. It is, however, only used internally. The difference is, that the pointer is on the stop symbol, instead of the start symbol. This predicate is useful for intermediate states of a machine, for example in the machine [CopyValue], which first has to move the head to the stop symbol. We write [t ≂ x] for [t] reversedly contains [x]. *)

  Section Tape_Contains.
    Variable (sigX : Type) (X : Type) (cX : codable sigX X) (I : Retract sigX sig).

    Definition tape_contains (t: tape sig^+) (x : X) :=
      exists r1, t = midtape r1 (inl START) (map inr (Encode_map _ _ x) ++ [inl STOP]).

    Definition tape_contains_size (t: tape sig^+) (x : X) (s : nat) :=
      exists r1, t = midtape r1 (inl START) (map inr (Encode_map _ _ x) ++ [inl STOP]) /\
            length r1 <= s.

    Definition tape_contains_rev (t: tape sig^+) (x : X) :=
      exists r1, t = midtape (map inr (rev (Encode_map _ _ x)) ++ inl START :: r1) (inl STOP) nil.

    Definition tape_contains_rev_size (t: tape sig^+) (x : X) (s : nat) :=
      exists r1, t = midtape (map inr (rev (Encode_map _ _ x)) ++ inl START :: r1) (inl STOP) nil /\
            length r1 <= s.

    Lemma tape_contains_rev_isRight t x :
      tape_contains_rev t x ->
      isRight t.
    Proof. intros (r1&->). repeat econstructor. Qed.

    Lemma tape_contains_rev_size_isRight t x s :
      tape_contains_rev_size t x s ->
      isRight_size t (S (size _ x + s)).
    Proof.
      intros (r1&->&Hs). hnf.
      do 2 eexists. repeat split. simpl_list. cbn. unfold size. simpl_list. omega.
    Qed.

    Lemma tape_contains_size_contains t x s :
      tape_contains_size t x s -> tape_contains t x.
    Proof. intros (r1&H1&H2). hnf; eauto. Qed.

    Lemma tape_contains_rev_size_contains t x s :
      tape_contains_rev_size t x s -> tape_contains_rev t x.
    Proof. intros (r1&H1&H2). hnf; eauto. Qed.

    Lemma tape_contains_contains_size t x :
      tape_contains t x -> tape_contains_size t x (length (left t)).
    Proof. intros (r1&->). cbn. hnf. eexists. split. reflexivity. reflexivity. Qed.

    Lemma tape_contains_rev_contains_rev_size t x :
      tape_contains_rev t x -> tape_contains_rev_size t x (length (left t) - S (size _ x)).
    Proof.
      intros (r1&->). cbn. hnf. eexists. split. reflexivity.
      apply Nat.eq_le_incl. simpl_list; cbn. unfold size. omega.
    Qed.

    Lemma tape_contains_size_sizeOfTape (t : tape (sig^+)) x s :
      tape_contains_size t x s ->
      sizeOfTape t <= 2 + s + size _ x.
    Proof. intros (rs&->&H). cbn. simpl_list; cbn. simpl_list; cbn. unfold size. omega. Qed.

    Lemma tape_contains_rev_size_sizeOfTape (t : tape (sig^+)) x s :
      tape_contains_rev_size t x s ->
      sizeOfTape t <= 2 + s + size _ x.
    Proof. intros (rs&->&H). cbn. simpl_list; cbn. simpl_list; cbn. unfold size. omega. Qed.

  End Tape_Contains.

  Arguments tape_contains {sigX X cX} (I t x) : simpl never.
  Arguments tape_contains_rev {sigX X cX} (I t x) : simpl never.
  Arguments tape_contains_size {sigX X cX} (I t x s) : simpl never.
  Arguments tape_contains_rev_size {sigX X cX} (I t x s) : simpl never.

  Notation "t ≃( I ) x" := (tape_contains I t x) (at level 70, no associativity).
  Notation "t ≃ x" := (t ≃(_) x) (at level 70, no associativity, only parsing).
  Notation "t ≃( I ';' s ) x" := (tape_contains_size I t x s) (at level 70, no associativity).
  Notation "t ≃( ';' s ) x" := (t ≃(_;s) x) (at level 70, only parsing).
  Notation "t ≂( I ) x" := (tape_contains_rev I t x) (at level 70, no associativity).
  Notation "t ≂ x" := (t ≃(_) x) (at level 70, no associativity, only parsing).
  Notation "t ≂( I ';' s ) x" := (tape_contains_rev_size I t x s) (at level 70, no associativity).
  Notation "t ≃( ';' s ) x" := (t ≃(_;s) x) (at level 70, no associativity, only parsing).

  Section Encodes_Ext.
    Variable (X Y sigX sigY : Type) (cX : codable sigX X) (cY : codable sigY Y) (I1 : Retract sigX sig) (I2 : Retract sigY sig).

    Lemma tape_contains_ext (t : tape (sig^+)) (x : X) (y : Y) :
      t ≃(I1) x ->
      Encode_map _ _ x = Encode_map _ _ y ->
      t ≃(I2) y.
    Proof. cbn. intros (r1&->). repeat econstructor. cbn. do 2 f_equal. now rewrite H. Qed.

    Lemma tape_contains_size_ext (t : tape (sig^+)) x y s1 s2 :
      t ≃(I1;s1) x ->
      Encode_map _ _ x = Encode_map _ _ y ->
      s1 <= s2 ->
      t ≃(I2;s2) y.
    Proof. cbn. intros (r1&->&Hs) H. repeat econstructor. cbn. do 2 f_equal. now rewrite H. omega. Qed.

    Lemma tape_contains_rev_ext (t : tape (sig^+)) (x : X) (y : Y) :
      t ≃(I1) x ->
      Encode_map _ _ x = Encode_map _ _ y ->
      t ≃(I2) y.
    Proof. cbn. intros (r1&->) H. repeat econstructor. cbn. do 2 f_equal. now rewrite H. Qed.

    Lemma tape_contains_rev_size_ext (t : tape (sig^+)) x y s1 s2 :
      t ≂(I1;s1) x ->
      Encode_map _ _ x = Encode_map _ _ y ->
      s1 <= s2 ->
      t ≂(I2;s2) y.
    Proof. cbn. intros (r1&->&Hs) H. repeat econstructor. cbn. do 2 f_equal. now rewrite H. omega. Qed.

  End Encodes_Ext.


  (** Define tapes that contain a value or are right. *)
  Section InitTape.
    Variable (sigX X : Type) (cX : codable sigX X) (I : Retract sigX sig).

    Definition initValue (x : X) :=
      midtape nil (inl START) (map inr (Encode_map _ _ x) ++ [inl STOP]).

    Lemma initValue_contains_size (x : X) :
      initValue x ≃(;0) x.
    Proof. unfold initValue. repeat econstructor. Qed.

    Lemma initValue_contains (x : X) :
      initValue x ≃ x.
    Proof. repeat econstructor. Qed.

    Definition initRight : tape sig^+ := midtape nil (inl STOP) nil.

    Lemma initRight_isRight_size : isRight_size (initRight) 0.
    Proof. repeat econstructor. Qed.

    Lemma initRight_isRight : isRight initRight.
    Proof. repeat econstructor. Qed.

  End InitTape.

End Fix_Sig.

Arguments tape_contains {sig sigX X cX} (I t x) : simpl never.
Arguments tape_contains_rev {sig sigX X cX} (I t x) : simpl never.
Arguments tape_contains_size {sig sigX X cX} (I t x s) : simpl never.
Arguments tape_contains_rev_size {sig sigX X cX} (I t x s) : simpl never.

Notation "t ≃( cX ) x" := (tape_contains cX t x) (at level 70, no associativity, format "t  ≃( cX )  x").
Notation "t ≃ x" := (t ≃(_) x) (at level 70, no associativity, only parsing).
Notation "t ≃( cX ';' s ) x" := (tape_contains_size cX t x s) (at level 70, no associativity, format "t  ≃( cX ';'  s )  x").
Notation "t ≃( ';' s ) x" := (t ≃(_;s) x) (at level 70, only parsing).

(* [≂] is only used "internally"! *)
Notation "t ≂( cX ) x" := (tape_contains_rev cX t x) (at level 70, no associativity, format "t  ≂( cX )  x").
Notation "t ≂ x" := (t ≂(_) x) (at level 70, no associativity, only parsing).
Notation "t ≂( cX ';' s ) x" := (tape_contains_rev_size cX t x s) (at level 70, no associativity, format "t  ≂( cX ';'  s )  x").
Notation "t ≂( ';' s ) x" := (t ≂(_;s) x) (at level 70, no associativity, only parsing).



(** The tactic [contains_ext] applys [tape_contains_ext] *)

Ltac contains_solve_le :=
  try now (cbn; solve [omega]).

Ltac contains_ext :=
  lazymatch goal with
  | [H : ?t ≃(_;?s1) ?x |- ?t ≃(_;?s2) ?y] =>
    apply tape_contains_size_ext with (1 := H); simpl_comp; try reflexivity; try contains_solve_le
  | [H : ?t ≃(_;?s1) ?x |- ?t ≃(_) ?y] =>
    eapply tape_contains_size_contains; contains_ext
  | [H : ?t ≃(_) ?x |- ?t ≃(_;?s2) ?y] =>
    eapply tape_contains_contains_size; contains_ext
  | [H : ?t ≃(_) ?x |- ?t ≃(_) ?y] =>
    apply tape_contains_ext with (1 := H); simpl_comp; try reflexivity
  (* [≂] is only used "internally"! *)
  | [H : ?t ≂(_;?s1) ?x |- ?t ≂(_;?s2) ?y] =>
    apply tape_contains_rev_size_ext with (1 := H); simpl_comp; try reflexivity; contains_solve_le
  | [H : ?t ≂(_;?s1) ?x |- ?t ≂(_) ?y] =>
    eapply tape_contains_rev_size_contains; contains_ext
  | [H : ?t ≂(_) ?x |- ?t ≂(_;?s2) ?y] =>
    eapply tape_contains_rev_contains_rev_size; contains_ext
  | [H : ?t ≂(_) ?x |- ?t ≂(_) ?y] =>
    apply tape_contains_rev_ext with (1 := H); simpl_comp; try reflexivity
  end.

Hint Extern 10 => contains_ext : core.


(** Because every machine is defined on an alphabet [Σ^+], the notation adds the discreteness and finiteness constructors, to cast [Σ^+ : finType]. *)
Notation "sig '^+'" := (FinType (EqType (boundary + sig) % type)) (at level 0) : type_scope.




(** Size functions are functions of type [Vector.t (nat->nat) n]. They compute the memory usage (i.e. size of the left rest) on a tape, given its initial size value *)

(** Compose two size functions *)
Definition compSizeFun (n : nat) (f1 f2 : Vector.t (nat -> nat) n) : Vector.t (nat -> nat) n :=
  tabulate (fun i => f1[@i] >> f2[@i]).

Notation "f >>> g" := (compSizeFun f g) (at level 40).

(** Get the size function of a tape *)
Notation "s '@>' i" := (s[@i]) (at level 10, only parsing).

(** You can write [size_function values... @>Fin1 s0], which is equivialent to [(size_function values...)[@Fin1] s0], i.e. the evaluation of the size function [size_function values...] on tape 1. *)


(** Tapes-lift for size functions *)

Definition injectSizeFun {m n : nat} (f : Vector.t (nat->nat) m) (I : Vector.t (Fin.t n) m) : Vector.t (nat->nat) n :=
  LiftTapes.fill I (Vector.const id _) f.

Notation "f '@>>' I" := (injectSizeFun f I) (at level 41).

(** You can write [ f1 @>> I1 >>> f2 @>>> I2], which is equivialent to [(f1 @>> I1) >>> (f2 @>> I2)], i.e. we lift [f1] with [I2] and compose this with the lifting of [f2]. *)
(* FIXME: this doesn't work yet. Use parenthesis *)
