(** * Basis for the full TM library *)

(** This file imports all shared libraries and defines [loop], lemmas about [loop], and some auxiliay functions. *)

Require Export Undecidability.Shared.Libs.PSL.FiniteTypes.FinTypes Undecidability.Shared.Libs.PSL.FiniteTypes.BasicFinTypes Undecidability.Shared.Libs.PSL.FiniteTypes.CompoundFinTypes Undecidability.Shared.Libs.PSL.FiniteTypes.VectorFin.
Require Export Undecidability.Shared.Libs.PSL.Vectors.FinNotation.
Require Export Undecidability.Shared.Libs.PSL.Retracts.
Require Export Undecidability.Shared.Libs.PSL.Inhabited.
Require Export Undecidability.Shared.Libs.PSL.Base.
Require Export Undecidability.Shared.Libs.PSL.Vectors.Vectors Undecidability.Shared.Libs.PSL.Vectors.VectorDupfree.

Require Export smpl.Smpl Lia.

Global Open Scope vector_scope.


Section Loop.
  Variable (A : Type) (f : A -> A) (p : A -> bool).

  Fixpoint loop (a : A) (k : nat) {struct k} :=
    if p a then Some a else
      match k with
      | O => None
      | S k' => loop (f a) k'
      end.

  Lemma loop_step k a :
    p a = false ->
    loop a (S k) = loop (f a) k.
  Proof. intros HHalt. destruct k; cbn; rewrite HHalt; auto. Qed.

  Lemma loop_injective k1 k2 a b b' :
    loop a k1 = Some b ->
    loop a k2 = Some b' ->
    b = b'.
  Proof.
    revert k2 b b' a. induction k1; intros; cbn in *.
    - destruct (p a) eqn:E; inv H.
      destruct k2; cbn in H0; rewrite E in H0; now inv H0.
    - destruct (p a) eqn:E.
      + inv H. destruct k2; cbn in H0; rewrite E in H0; now inv H0.
      + destruct k2; cbn in H0; rewrite E in H0; try now inv H0.
        eauto.
  Qed.

  Lemma loop_fulfills k a b :
    loop a k = Some b ->
    p b = true.
  Proof.
    revert a; induction k; intros; cbn in *.
    - now destruct (p a) eqn:E; inv H.
    - destruct (p a) eqn:E.
      + now inv H.
      + eapply IHk; eauto.
  Qed.

  Lemma loop_0 k a :
    p a = true ->
    loop a k = Some a.
  Proof. intros. destruct k; cbn; now rewrite H. Qed.

  Lemma loop_eq_0 k a b :
    p a = true ->
    loop a k = Some b ->
    b = a.
  Proof. intros H1 H2. eapply (loop_0 k) in H1. congruence. Qed.

  Lemma loop_monotone (k1 k2 : nat) (a b : A) : loop a k1 = Some b -> k1 <= k2 -> loop a k2 = Some b.
  Proof.
    revert a k2; induction k1 as [ | k1' IH]; intros a k2 HLoop Hk; cbn in *.
    - destruct k2; cbn; destruct (p a); now inv HLoop.
    - destruct (p a) eqn:E.
      + inv HLoop. now apply loop_0.
      + destruct k2 as [ | k2']; cbn in *; rewrite E.
        * exfalso. lia.
        * apply IH. assumption. lia.
  Qed.

End Loop.


Section LoopLift.

  Variable A B : Type. (** Abstract state *)
  Variable lift : A -> B. (** Lifting function between state *)
  Variable (f : A -> A) (f' : B -> B). (** Abstract steps *)
  Variable (h : A -> bool) (h' : B -> bool). (** Abstract halting state *)

  Hypothesis halt_lift_comp : forall x:A, h' (lift x) = h x.
  Hypothesis step_lift_comp : forall x:A, h x = false -> f' (lift x) = lift (f x).

  Lemma loop_lift (k : nat) (a a' : A) :
    loop (A := A) f  h  a        k = Some a' ->
    loop (A := B) f' h' (lift a) k = Some (lift a').
  Proof.
    revert a. induction k as [ | k']; intros; cbn in *.
    - rewrite halt_lift_comp. destruct (h a); now inv H.
    - rewrite halt_lift_comp. destruct (h a) eqn:E.
      + now inv H.
      + rewrite step_lift_comp by auto. now apply IHk'.
  Qed.

  Lemma loop_unlift (k : nat) (a : A) (b' : B) :
    loop f' h' (lift a) k = Some b' ->
    exists a' : A, loop f h a k = Some a' /\ b' = lift a'.
  Proof.
    revert a b'. induction k as [ | k']; intros; cbn in *.
    - rewrite halt_lift_comp in H.
      exists a. destruct (h a) eqn:E; now inv H.
    - rewrite halt_lift_comp in H.
      destruct (h a) eqn:E.
      + exists a. now inv H.
      + rewrite step_lift_comp in H by assumption.
        specialize IHk' with (1 := H) as (x&IH&->). now exists x.
  Qed.
    
End LoopLift.


Section LoopMerge.

  Variable A : Type. (** abstract state *)
  Variable f : A -> A. (** abstract step function *)
  Variable (h h' : A -> bool). (** abstract halting functions *)

  (** Every non-halting state w.r.t. [h] is also a non-halting state w.r.t. [h'] *)
  Hypothesis halt_comp : forall a, h a = false -> h' a = false.

  Lemma loop_merge (k1 k2 : nat) (a1 a2 a3 : A) :
    loop f h  a1 k1      = Some a2 ->
    loop f h' a2 k2      = Some a3 ->
    loop f h' a1 (k1+k2) = Some a3.
  Proof.
    revert a1 a2 a3. induction k1 as [ | k1' IH]; intros a1 a2 a3 HLoop1 HLoop2; cbn in HLoop1.
    - now destruct (h a1); inv HLoop1.
    - destruct (h a1) eqn:E.
      + inv HLoop1. eapply loop_monotone; eauto. lia.
      + cbn. rewrite (halt_comp E). eapply IH; eauto.
  Qed.

  Lemma loop_split (k : nat) (a1 a3 : A) :
    loop f h' a1 k = Some a3 ->
    exists k1 a2 k2,
      loop f h  a1 k1 = Some a2 /\
      loop f h' a2 k2 = Some a3 /\
      k1 + k2 <= k.
  Proof.
    revert a1 a3. revert k; refine (size_recursion id _); intros k IH. intros a1 a3 HLoop. cbv [id] in *.
    destruct k as [ | k']; cbn in *.
    - destruct (h' a1) eqn:E; inv HLoop.
      exists 0, a3, 0. cbn. rewrite E.
      destruct (h a3) eqn:E'.
      + auto.
      + apply halt_comp in E'. congruence.
    - destruct (h a1) eqn:E.
      + exists 0, a1, (S k'). cbn. rewrite E. auto.
      + rewrite (halt_comp E) in HLoop.
        apply IH in HLoop as (k1&c2&k2&IH1&IH2&IH3); [ | lia].
        exists (S k1), c2, k2. cbn. rewrite E. repeat split; auto. lia.
  Qed.
  
End LoopMerge.


(** Apply functions in tuples, options, etc. *)
Section Map.
  Variable X Y Z : Type.

  Definition map_opt : (X -> Y) -> option X -> option Y :=
    fun f a =>
      match a with
      | Some x => Some (f x)
      | None => None
      end.

  Definition map_inl : (X -> Y) -> X + Z -> Y + Z :=
    fun f a =>
      match a with
      | inl x => inl (f x)
      | inr y => inr y
      end.

  Definition map_inr : (Y -> Z) -> X + Y -> X + Z :=
    fun f a =>
      match a with
      | inl y => inl y
      | inr x => inr (f x)
      end.

  Definition map_fst : (X -> Z) -> X * Y -> Z * Y := fun f '(x,y) => (f x, y).
  Definition map_snd : (Y -> Z) -> X * Y -> X * Z := fun f '(x,y) => (x, f y).

End Map.



(** Function composition *)

(* Function composition in the standard mathematical way *)
Definition funcomp {X Y Z : Type} (g : Y -> Z) (f : X -> Y) : X -> Z := fun x => g (f x).

Arguments funcomp {X Y Z} (g f) x/.

(*
Eval cbn in funcomp id id.
Eval cbn in funcomp id id 1.
*)

Notation "g >> f" := (funcomp f g) (at level 40).




(** We often use the vernacular commands
<<
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.
>>
to avoid unfolding [*] and [+] in running time polynoms. However, this can break proofs that use [Fin.R], since the [plus] in the type of [Fin.R] doesn't simplify with [cbn] any more. To work around this problem, we have a copy of [Fin.R] and [plus], that isn't affected by these commands. *)

Fixpoint plus' (n m : nat) { struct n } : nat :=
  match n with
  | 0 => m
  | S p => S (plus' p m)
  end.

Fixpoint FinR {m} n (p : Fin.t m) : Fin.t (plus' n m) :=
  match n with
  | 0 => p
  | S n' => Fin.FS (FinR n' p)
  end.



(** Folding for options *)
Definition fold_opt (X Y : Type) : (X -> Y) -> Y -> option X -> Y :=
  fun f def o => match o with
              | Some o' => f o'
              | None => def
              end.


Lemma map_opt_fold (X Y : Type) (f : X -> Y) (x : option X) :
  map_opt f x = fold_opt (fun x => Some (f x)) None x.
Proof. intros. destruct x; cbn; reflexivity. Qed.
