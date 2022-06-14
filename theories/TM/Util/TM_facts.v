(* * Definition of Multi-Tape Turing Machines *)

(* Definitions of tapes and (unlabelled) multi-tape Turing machines from Asperti, Riciotti "A formalization of multi-tape Turing machines" (2015) and the accompanying Matita code. *)

From Undecidability.TM.Util Require Export Prelim Relations.
Require Import Undecidability.Shared.Libs.PSL.Vectors.Vectors.
Require Export Undecidability.TM.TM.

Section Fix_Sigma.

  Variable sig : Type.

  Notation tape := (tape sig).

  (* ** Definition of the tape *)
  
  (* A tape is essentially a triple 〈left,current,right〉 where, however, the current symbol could be missing. This may happen for three different reasons: both tapes are empty, we are on the left extremity of a non-empty tape (left overflow), or we are on the right extremity of a non-empty tape (right overflow). *)

  (* Note that the alphabet has type [Type], not [finType]. *)
  (* Print tape. *)

  Definition tapes n := Vector.t tape n.

  Definition tapeToList (t : tape) : list sig :=
    match t with
    | niltape => []
    | leftof s r => s :: r
    | rightof s l => List.rev (s :: l)
    | midtape l c r => (List.rev l) ++ [c] ++ r 
    end.

  Definition left :=
    fun (t : tape) =>
      match t with
      | niltape => []
      | leftof _ _ => []
      | rightof s l => s :: l
      | midtape l _ _ => l
      end.

  Definition right :=
    fun (t : tape) =>
      match t with
      | niltape => []
      | leftof s r => s :: r
      | rightof _ _ => []
      | midtape _ _ r => r
      end.

  (* Lemmas for [midtape] *)
  Lemma tape_midtape_current_right t rs s :
    current t = Some s ->
    right t = rs ->
    t = midtape (left t) s rs.
  Proof. destruct t; cbn; congruence. Qed.

  Lemma tape_midtape_current_left t ls s :
    current t = Some s ->
    left t = ls ->
    t = midtape ls s (right t).
  Proof. destruct t; cbn; congruence. Qed.

  Lemma tape_is_midtape t ls s rs :
    left t = ls ->
    current t = Some s ->
    right t = rs ->
    t = midtape ls s rs.
  Proof. destruct t; cbn; congruence. Qed.
  
  
  (* ** Definition of moves *)
  
  (* Print move.  *)

  (* Declare discreteness of [move] *)
  Global Instance move_eq_dec : eq_dec move.
  Proof.
    intros. hnf. decide equality.
  Defined. (* because definition *)

  (* Declare finiteness of [move] *)
  Global Instance move_finC : finTypeC (EqType move).
  Proof.
    apply (FinTypeC (enum := [Lmove; Rmove; Nmove])).
    intros []; now cbv.
  Defined. (* because definition *)

  (* We outsource the second [match] of [tape_move_right] in the [midtape] case to another named definition. This has the advantage that the [cbn] tactic will not reduce [tape_move_left (midtape ls m rs)] to a long term that contains [match]. It reduces to [tape_move_left' ls m rs] instead. Furthermore, there are rewrite lemmas available for [tape_move_left']. *)

  Definition tape_move_right' ls a rs : tape :=
    match rs with
    | nil => rightof a ls
    | r::rs' => midtape (a::ls) r rs'
    end.

  Definition tape_move_right :=
    fun (t : tape) =>
      match t with
      | niltape => niltape
      | rightof _ _ =>t
      | leftof a rs =>midtape  [ ] a rs
      | midtape ls a rs => tape_move_right' ls a rs
      end.


  Definition tape_move_left' ls a rs : tape :=
    match ls with
    | nil => leftof a rs
    | l::ls' => midtape ls' l (a::rs)
    end.
  
  Definition tape_move_left :=
    fun (t : tape) =>
      match t with 
      | niltape => niltape 
      | leftof _ _ => t
      | rightof a ls => midtape ls a [ ]
      | midtape ls a rs => tape_move_left' ls a rs
      end. 


  Definition tape_move (t : tape) (m : move) :=
    match m with
    | Rmove => tape_move_right t
    | Lmove => tape_move_left t
    | Nmove => t
    end.

  (* *** Rewriting Lemmas *)

  Lemma tapeToList_move (t : tape) (D : move) :
    tapeToList (tape_move t D) = tapeToList t.
  Proof.
    destruct t, D; cbn; auto.
    - revert s l0. induction l; intros; cbn in *; simpl_list; auto.
    - revert s l. induction l0; intros; cbn in *; simpl_list; auto.
  Qed.

  Lemma tapeToList_move_R (t : tape) :
    tapeToList (tape_move_right t) = tapeToList t.
  Proof. apply (tapeToList_move t Rmove). Qed.

  Lemma tapeToList_move_L (t : tape) :
    tapeToList (tape_move_left t) = tapeToList t.
  Proof. apply (tapeToList_move t Lmove). Qed.

  Lemma tape_move_right_left (t : tape) (s : sig) :
    current t = Some s ->
    tape_move_left (tape_move_right t) = t.
  Proof.
    intros H1. destruct t; cbn in *; inv H1; auto; destruct l; auto; destruct l0; auto.
  Qed.

  Lemma tape_move_left_right (t : tape) (s : sig) :
    current t = Some s ->
    tape_move_right (tape_move_left t) = t.
  Proof.
    intros H1. destruct t; cbn in *; inv H1; auto; destruct l; auto; destruct l0; auto.
  Qed.


  (* ** Machine step *)

  (* Writing on the tape *)
  Definition tape_write (t : tape) (s : option sig) :=
    match s with 
    | None => t
    | Some s' => midtape (left t) s' (right t)
    end.

  (* A single step of the machine *)
  Definition doAct (t : tape) (mv : option sig * move) :=
    tape_move (tape_write t (fst mv)) (snd mv).

  (* One step on each tape *)
  Definition doAct_multi (n : nat) (ts : tapes n) (actions : Vector.t (option sig * move) n) :=
    Vector.map2 doAct ts actions.

  (* Read characters on all tapes *)
  Definition current_chars (n : nat) (tapes : tapes n) := Vector.map current tapes.

End Fix_Sigma.


(* ** Rewriting tactics *)


(* Tactic to destruct a vector of tapes of known size *)
Ltac destruct_tapes := unfold tapes in *; destruct_vector.

(* Simplification Database for tapes and vectors *)
Create HintDb tape.
Create HintDb vector.

(* We use [rewrite_strat] instead of [autorewrite], because it is faster. *)
Tactic Notation "simpl_tape" :=
  repeat rewrite_strat (topdown (choice (hints tape) (hints vector))).
Tactic Notation "simpl_tape" "in" ident(H) :=
  repeat rewrite_strat (topdown (choice (hints tape) (hints vector))) in H.
Tactic Notation "simpl_tape" "in" "*" :=
  repeat multimatch goal with
         | [ H : _ |- _ ] => simpl_tape in H
         end;
  simpl_tape.

Tactic Notation "simpl_vector" :=
  repeat rewrite_strat (topdown (hints vector)).
Tactic Notation "simpl_vector" "in" ident(H) :=
  repeat rewrite_strat (topdown (hints vector)) in H.
Tactic Notation "simpl_vector" "in" "*" :=
  repeat multimatch goal with
         | [ H : _ |- _ ] => simpl_vector in H
         end;
  simpl_vector.


Global Hint Rewrite tapeToList_move : tape.
Global Hint Rewrite tapeToList_move_R : tape.
Global Hint Rewrite tapeToList_move_L : tape.
Global Hint Rewrite tape_move_right_left using eauto : tape.
Global Hint Rewrite tape_move_left_right using eauto : tape.

Arguments current_chars : simpl never.
#[export] Hint Unfold current_chars : tape.



Lemma nth_map' (A B : Type) (f : A -> B) (n : nat) (v : Vector.t A n) (k : Fin.t n) :
  (VectorDef.map f v)[@k] = f v[@k].
Proof. erewrite VectorSpec.nth_map; eauto. Qed.

Lemma nth_map2' (A B C : Type) (f : A -> B -> C) (n : nat) (v1 : Vector.t A n) (v2 : Vector.t B n) (k : Fin.t n) :
  (VectorDef.map2 f v1 v2)[@k] = f v1[@k] v2[@k].
Proof. erewrite VectorSpec.nth_map2; eauto. Qed.

Global Hint Rewrite @nth_map' : vector.
Global Hint Rewrite @nth_map2' : vector.
Global Hint Rewrite @nth_tabulate : vector.
Global Hint Rewrite VectorSpec.const_nth : vector.



(* Set Notation scopes for tapes, so that the alphabet of the tape is parsed as a type (e.g. [X+Y] is parsed as the sum type, not the addition of [X] and [Y]) *)
Arguments tapes (sig % type) (n % nat).


(* ** Nop Action *)

(* (∅, Nmove)^n *)
Section Nop_Action.
  Variable n : nat.
  Variable sig : finType.

  Definition nop_action := Vector.const (@None sig, Nmove) n.

  Lemma doAct_nop tapes :
    doAct_multi tapes nop_action = tapes.
  Proof.
    unfold nop_action, doAct_multi.
    apply Vector.eq_nth_iff; intros ? i <-.
    erewrite Vector.nth_map2; eauto.
    rewrite Vector.const_nth.
    cbn. reflexivity.
  Qed.

End Nop_Action.

(* Make [n] and [sig] contextual implicit *)
Arguments nop_action {_ _}.





(* ** Mirror tapes *)

Section MirrorTape.
  Variable (n : nat) (sig : Type).

  Definition mirror_tape (t : tape sig) : tape sig :=
    match t with
    | niltape _ => niltape _
    | leftof r rs => rightof r rs
    | rightof l ls => leftof l ls
    | midtape ls m rs => midtape rs m ls
    end.

  Lemma mirror_tape_left (t : tape sig) :
    left (mirror_tape t) = right t.
  Proof. now destruct t. Qed.

  Lemma mirror_tape_right (t : tape sig) :
    right (mirror_tape t) = left t.
  Proof. now destruct t. Qed.

  Lemma mirror_tape_current (t : tape sig) :
    current (mirror_tape t) = current t.
  Proof. now destruct t. Qed.

  Lemma mirror_tape_involution (t : tape sig) :
    mirror_tape (mirror_tape t) = t.
  Proof. destruct t; cbn; congruence. Qed.

  Lemma mirror_tape_injective (t1 t2 : tape sig) :
    mirror_tape t1 = mirror_tape t2 ->
    t1 = t2.
  Proof. destruct t1, t2; intros H; cbn in *; congruence. Qed.


  Lemma mirror_tape_move_left (t : tape sig) :
    mirror_tape (tape_move_left t) = tape_move_right (mirror_tape t).
  Proof. destruct t; cbn; auto. destruct l; cbn; auto. Qed.

  Lemma mirror_tape_move_right (t : tape sig) :
    mirror_tape (tape_move_right t) = tape_move_left (mirror_tape t).
  Proof. destruct t; cbn; auto. destruct l0; cbn; auto. Qed.


  Lemma mirror_tape_inv_midtape t r1 r2 x :
    mirror_tape t = midtape r1 x r2 -> t = midtape r2 x r1.
  Proof. intros. destruct t; cbn in *; congruence. Qed.

  Lemma mirror_tape_inv_leftof t rs x :
    mirror_tape t = leftof rs x -> t = rightof rs x.
  Proof. intros. destruct t; cbn in *; congruence. Qed.

  Lemma mirror_tape_inv_rightof t ls x :
    mirror_tape t = rightof ls x -> t = leftof ls x.
  Proof. intros. destruct t; cbn in *; congruence. Qed.

  Lemma mirror_tape_inv_niltape t :
    mirror_tape t = niltape _  -> t = niltape _.
  Proof. intros. destruct t; cbn in *; congruence. Qed.

  Lemma mirror_tape_inv_midtape' t r1 r2 x :
    midtape r1 x r2 = mirror_tape t -> t = midtape r2 x r1.
  Proof. intros. destruct t; cbn in *; congruence. Qed.

  Lemma mirror_tape_inv_leftof' t rs x :
    leftof rs x = mirror_tape t -> t = rightof rs x.
  Proof. intros. destruct t; cbn in *; congruence. Qed.

  Lemma mirror_tape_inv_rightof' t ls x :
    rightof ls x = mirror_tape t -> t = leftof ls x.
  Proof. intros. destruct t; cbn in *; congruence. Qed.

  Lemma mirror_tape_inv_niltape' t :
    niltape _ = mirror_tape t -> t = niltape _.
  Proof. intros. destruct t; cbn in *; congruence. Qed.


  Definition mirror_tapes (t : tapes sig n) : tapes sig n := Vector.map mirror_tape t.

  Lemma mirror_tapes_involution (t : tapes sig n) :
    mirror_tapes (mirror_tapes t) = t.
  Proof.
    unfold mirror_tapes. apply Vector.eq_nth_iff. intros ? ? ->.
    erewrite !Vector.nth_map; eauto. apply mirror_tape_involution.
  Qed.

  Lemma mirror_tapes_injective (t1 t2 : tapes sig n) :
    mirror_tapes t1 = mirror_tapes t2 ->
    t1 = t2.
  Proof.
    intros H. unfold mirror_tapes in *. apply Vector.eq_nth_iff. intros ? ? ->.
    eapply Vector.eq_nth_iff with (p1 := p2) in H; eauto.
    erewrite !Vector.nth_map in H; eauto. now apply mirror_tape_injective.
  Qed.
  
  Definition mirror_move (D : move) : move := match D with | Nmove => Nmove | Lmove => Rmove | Rmove => Lmove end.

  Lemma mirror_move_involution (D : move) : mirror_move (mirror_move D) = D.
  Proof. now destruct D. Qed.

  Lemma mirror_tapes_nth (tapes : tapes sig n) (k : Fin.t n) :
    (mirror_tapes tapes)[@k] = mirror_tape (tapes[@k]).
  Proof. intros. eapply VectorSpec.nth_map; eauto. Qed.

End MirrorTape.

Arguments mirror_tapes : simpl never.
#[export] Hint Unfold mirror_tapes : tape.

Global Hint Rewrite mirror_tape_left : tape.
Global Hint Rewrite mirror_tape_right : tape.
Global Hint Rewrite mirror_tape_current : tape.
Global Hint Rewrite mirror_tape_involution : tape.
Global Hint Rewrite mirror_tape_move_left : tape.
Global Hint Rewrite mirror_tape_move_right : tape.
Global Hint Rewrite mirror_tapes_involution : tape.
Global Hint Rewrite mirror_tapes_nth : tape.



(* ** Helping functions for tapes *)

Section Tape_Local.

  Variable sig : Type.

  (* The current symbol :: right symbols *)
  Definition tape_local (t : tape sig) : list sig :=
    match t with
    | niltape _ => []
    | leftof a l => []
    | rightof _ _ => []
    | midtape _ a l => a :: l
    end.

  (* The current symbol :: left symbols *)
  Definition tape_local_l (t : tape sig) : list sig :=
    match t with
    | niltape _ => []
    | leftof a l => []
    | rightof _ _ => []
    | midtape r a l => a :: r
    end.

  Lemma tape_local_mirror (t : tape sig) :
    tape_local_l (mirror_tape t) = tape_local t.
  Proof. destruct t; cbn; auto. Qed.

  Lemma tape_local_mirror' (t : tape sig) :
    tape_local (mirror_tape t) = tape_local_l t.
  Proof. destruct t; cbn; auto. Qed.
    
  Lemma tape_local_current_cons (x : sig) (xs : list sig) (t : tape sig) :
    tape_local t = x :: xs -> current t = Some x.
  Proof. destruct t eqn:E; cbn; congruence. Qed.

  Lemma tape_local_l_current_cons (x : sig) (xs : list sig) (t : tape sig) :
    tape_local_l t = x :: xs -> current t = Some x.
  Proof. destruct t eqn:E; cbn; congruence. Qed.

  Lemma tape_local_right (x : sig) (xs : list sig) (t : tape sig) :
    tape_local t = x :: xs -> right t = xs.
  Proof. destruct t eqn:E; cbn; congruence. Qed.

  Lemma tape_local_l_left (x : sig) (xs : list sig) (t : tape sig) :
    tape_local_l t = x :: xs -> left t = xs.
  Proof. destruct t eqn:E; cbn; congruence. Qed.

  Lemma tape_local_cons_iff (t : tape sig) (x : sig) (xs : list sig) :
    tape_local t = x :: xs <-> current t = Some x /\ right t = xs.
  Proof.
    split; intros H.
    - destruct t; cbn in *; inv H. eauto.
    - destruct t; cbn in *; inv H; inv H0. eauto.
  Qed.

  Lemma tape_local_l_cons_iff (t : tape sig) (x : sig) (xs : list sig) :
    tape_local_l t = x :: xs <-> current t = Some x /\ left t = xs.
  Proof.
    split; intros H.
    - destruct t; cbn in *; inv H. eauto.
    - destruct t; cbn in *; inv H; inv H0. eauto.
  Qed.

  
  Lemma tape_local_nil (t : tape sig) :
    tape_local t = [] <-> current t = None.
  Proof.
    destruct t; cbn; intuition; auto; congruence.
  Qed.

  Lemma tape_local_move_right (t : tape sig) (x : sig) (xs : list sig) :
    tape_local t = x :: xs -> tape_local (tape_move_right t) = xs.
  Proof.
    intro H. destruct t eqn:E; cbn in *; try congruence.
    inv H. destruct xs; cbn; auto.
  Qed.

  Lemma tape_local_l_move_left (t : tape sig) (x : sig) (xs : list sig) :
    tape_local_l t = x :: xs -> tape_local_l (tape_move_left t) = xs.
  Proof.
    intro H. destruct t eqn:E; cbn in *; try congruence.
    inv H. destruct xs; cbn; auto.
  Qed.
  
  Lemma tape_left_move_right (t : tape sig) (x : sig) :
    current t = Some x -> left (tape_move_right t) = x :: left t.
  Proof. intros H. destruct t; cbn in *; try congruence. inv H. destruct l0; cbn; reflexivity. Qed.

  Lemma tape_right_move_left (t : tape sig) (x : sig) :
    current t = Some x -> right (tape_move_left t) = x :: right t.
  Proof. intros H. destruct t; cbn in *; try congruence. inv H. destruct l; cbn; reflexivity. Qed.

  Lemma midtape_tape_local_cons t r2 x :
    tape_local t = x :: r2 <-> t = midtape (left t) x r2.
  Proof.
    split.
    - intros H1. destruct t; cbn in *; congruence.
    - intros H1. destruct t; cbn in *; inv H1. auto.
  Qed.
  
  Lemma midtape_tape_local_cons_left t r1 r2 x :
    left t = r1 /\ tape_local t = x :: r2 <-> t = midtape r1 x r2.
  Proof. rewrite midtape_tape_local_cons. intuition subst; cbn; auto. Qed.

  
  Lemma midtape_tape_local_l_cons t r1 x :
    tape_local_l t = x :: r1 <-> t = midtape r1 x (right t).
  Proof.
    split.
    - intros H1. destruct t; cbn in *; congruence.
    - intros H1. destruct t; cbn in *; inv H1. auto.
  Qed.
  
  Lemma midtape_tape_local_l_cons_right t r1 r2 x :
    tape_local_l t = x :: r1 /\ right t = r2 <-> t = midtape r1 x r2.
  Proof. rewrite midtape_tape_local_l_cons. intuition subst; cbn; auto. Qed.

End Tape_Local.

Global Hint Rewrite tape_local_mirror  : tape.
Global Hint Rewrite tape_local_mirror' : tape.
Global Hint Rewrite tape_local_current_cons using auto : tape.
Global Hint Rewrite tape_local_l_current_cons using auto : tape.
Global Hint Rewrite tape_local_right        using auto : tape.
Global Hint Rewrite tape_local_l_left        using auto : tape.
Global Hint Rewrite tape_left_move_right    using auto : tape.
Global Hint Rewrite tape_right_move_left    using auto : tape.


(* ** Mapping tapes *)

(* Apply a function to each symbol on the tape *)
Section MapTape.
  Variable sig tau : Type.
  Variable g : tau -> sig.

  Definition mapTape : tape tau -> tape sig.
  Proof using g.
    destruct 1 eqn:E1.
    - apply niltape.
    - apply leftof.  apply (g t). apply (List.map g l).
    - apply rightof. apply (g t). apply (List.map g l).
    - apply midtape. apply (List.map g l). apply (g t). apply (List.map g l0).
  Defined. (* because definition *)

  Definition mapTapes {n : nat} : Vector.t (tape tau) n -> Vector.t (tape sig) n := Vector.map mapTape.

  (* Correctness of mapTape *)

  Lemma mapTape_current t :
    current (mapTape t) = map_opt g (current t).
  Proof. destruct t; cbn; reflexivity. Qed.

  Lemma mapTape_left t :
    left (mapTape t) = List.map g (left t).
  Proof. destruct t; cbn; reflexivity. Qed.

  Lemma mapTape_right t :
    right (mapTape t) = List.map g (right t).
  Proof. destruct t; cbn; reflexivity. Qed.

  Lemma mapTape_move_left t :
    tape_move_left (mapTape t) = mapTape (tape_move_left t).
  Proof. destruct t; cbn; auto. destruct l; cbn; auto. Qed.

  Lemma mapTape_move_right t :
    tape_move_right (mapTape t) = mapTape (tape_move_right t).
  Proof. destruct t; cbn; auto. destruct l0; cbn; auto. Qed.

  Lemma mapTape_inv_niltap t :
    mapTape t = niltape _ ->
    t = niltape _.
  Proof. intros. destruct t; inv H. repeat econstructor. Qed.

  Lemma mapTape_inv_rightof t l ls :
    mapTape t = rightof l ls ->
    exists l' ls', t = rightof l' ls' /\
              l = g l' /\
              ls = map g ls'.
  Proof. intros. destruct t; inv H. repeat econstructor. Qed.

  Lemma mapTape_inv_leftof t r rs :
    mapTape t = leftof r rs ->
    exists r' rs', t = leftof r' rs' /\
              r = g r' /\
              rs = map g rs'.
  Proof. intros. destruct t; inv H. repeat econstructor. Qed.

  Lemma mapTape_inv_midtape t ls m rs :
    mapTape t = midtape ls m rs ->
    exists ls' m' rs', t = midtape ls' m' rs' /\
                  ls = map g ls' /\
                  m = g m' /\
                  rs = map g rs'.
  Proof. intros. destruct t; inv H. repeat econstructor. Qed.

  (*
  Lemma mapTapes_nth {n : nat} (ts : tapes tau n) (k : Fin.t n) :
    (mapTapes ts)[@k] = mapTape (ts[@k]).
  Proof. unfold mapTapes. eapply VectorSpec.nth_map; eauto. Qed.
   *)

End MapTape.

(* Rewriting Hints *)

Global Hint Rewrite mapTape_current    : tape.
Global Hint Rewrite mapTape_left       : tape.
Global Hint Rewrite mapTape_right      : tape.
Global Hint Rewrite mapTape_move_left  : tape.
Global Hint Rewrite mapTape_move_right : tape.
(* Hint Rewrite mapTapes_nth       : tape. *)
#[export] Hint Unfold mapTapes : tape.


Lemma mapTape_mapTape (sig tau gamma : Type) (f : sig -> tau) (g : tau -> gamma) (t : tape sig) :
  mapTape g (mapTape f t) = mapTape (fun x => g (f x)) t.
Proof. destruct t; cbn; auto; try simpl_tape; now rewrite !map_map. Qed.

Lemma mapTape_ext (sig tau : Type) (f g : sig -> tau) (t : tape sig) :
  (forall a, f a = g a) -> mapTape f t = mapTape g t.
Proof. intros H. destruct t; cbn; auto; simpl_tape; rewrite H; f_equal; eapply map_ext; eauto. Qed.

Lemma mapTape_id (sig : Type) (t : tape sig) :
  mapTape (fun x => x) t = t.
Proof. destruct t; cbn; auto; f_equal; apply map_id. Qed.
Global Hint Rewrite mapTape_mapTape : tape.
Global Hint Rewrite mapTape_id : tape.


Lemma mapTape_local (sig tau : Type) (f : sig -> tau) t :
  tape_local (mapTape f t) = List.map f (tape_local t).
Proof. destruct t; cbn; reflexivity. Qed.
Global Hint Rewrite mapTape_local : tape.



(* ** Lemmas about [tape_move_left'] and [tape_move_right'] *)
Section MatchTapes.
  Variable sig : Type.

  (* Left movement *)

  Lemma tape_left_move_left' ls (x : sig) rs :
    left (tape_move_left' ls x rs) = tl ls.
  Proof. now destruct ls; cbn. Qed.

  Lemma tape_left_move_left (t : tape sig) :
    left (tape_move_left t) = tl (left t).
  Proof. destruct t; cbn; auto. apply tape_left_move_left'. Qed.

  Lemma tape_left_move_right' ls (x : sig) rs :
    left (tape_move_right' ls x rs) = x :: ls.
  Proof. destruct rs; cbn; reflexivity. Qed.
  
  Lemma tape_right_move_left' ls (x : sig) rs :
    right (tape_move_left' ls x rs) = x :: rs.
  Proof. destruct ls; cbn; reflexivity. Qed.

  Lemma tape_local_l_move_left' rs (x : sig) ls :
    tape_local_l (tape_move_left' rs x ls) = rs.
  Proof. destruct rs; cbn; reflexivity. Qed.

  Lemma mirror_tape_move_left' rs (x : sig) ls :
    mirror_tape (tape_move_left' rs x ls) = tape_move_right' ls x rs.
  Proof. now destruct rs; cbn. Qed.

  (* Right movement *)

  Lemma tape_right_move_right' ls (x : sig) rs :
    right (tape_move_right' ls x rs) = tl rs.
  Proof. now destruct rs; cbn. Qed.

  Lemma tape_right_move_right (t : tape sig) :
    right (tape_move_right t) = tl (right t).
  Proof. destruct t; cbn; auto. apply tape_right_move_right'. Qed.

  Lemma tape_local_move_right' rs (x : sig) ls :
    tape_local (tape_move_right' rs x ls) = ls.
  Proof. destruct ls; cbn; reflexivity. Qed.

  Lemma mirror_tape_move_right' rs (x : sig) ls :
    mirror_tape (tape_move_right' rs x ls) = tape_move_left' ls x rs.
  Proof. now destruct ls; cbn. Qed.
 

  Lemma tape_move_niltape (m : move) :
    tape_move (niltape sig) m = niltape sig.
  Proof. now destruct m. Qed.

  Lemma tape_write_left (t : tape sig) s :
    left (tape_write t s) = left t.
  Proof. destruct s; auto. Qed.

  Lemma tape_write_right (t : tape sig) s :
    right (tape_write t s) = right t.
  Proof. destruct s; auto. Qed.


  Lemma tape_write_current_Some (t : tape sig) s :
    current (tape_write t (Some s)) = Some s.
  Proof. auto. Qed.


  Lemma tape_write_current_None (t : tape sig) :
    current (tape_write t None) = current t.
  Proof. auto. Qed.

  Lemma tape_write_current (t : tape sig) s :
    current (tape_write t s) = fold_opt (@Some _) (current t) s.
  Proof. destruct s; auto. Qed.

End MatchTapes.

Global Hint Rewrite tape_left_move_left' : tape.
Global Hint Rewrite tape_left_move_left : tape.
Global Hint Rewrite tape_left_move_right' : tape.
Global Hint Rewrite tape_right_move_left' : tape.
Global Hint Rewrite tape_local_l_move_left' : tape.
Global Hint Rewrite mirror_tape_move_left' : tape.

Global Hint Rewrite tape_right_move_right' : tape.
Global Hint Rewrite tape_right_move_right : tape.
Global Hint Rewrite tape_right_move_left' : tape.
Global Hint Rewrite tape_right_move_right' : tape.
Global Hint Rewrite tape_local_move_right' : tape.
Global Hint Rewrite mirror_tape_move_right' : tape.

Global Hint Rewrite tape_move_niltape tape_write_left tape_write_right tape_write_current_Some tape_write_current_None tape_write_current : tape.




(* ** Definition of Multi-Tape Turing Machines *)
Section Semantics.

  Variable sig : finType.
  
  Notation TM := (TM sig).
  (* Labelled Multi-Tape Turing Machines *)
  Definition pTM (F: Type) (n:nat) := { M : TM n & state M -> F }.
  

  (* *** Configurations of TMs *)
  
  Record mconfig (state:finType) (n:nat): Type :=
    mk_mconfig
      {
        cstate : state;
        ctapes : tapes sig n
      }.


  (* *** Machine execution *)
  
  Definition step {n} (M:TM n) : mconfig (state M) n -> mconfig (state M) n :=
    fun c =>
      let (news,actions) := trans (cstate c, current_chars  (ctapes c)) in 
      mk_mconfig news (doAct_multi (ctapes c) actions).

  Definition haltConf {n} (M : TM n) : mconfig (state M) n -> bool := fun c => halt (cstate c).

  (* Run the machine i steps until it halts *)
  Definition loopM n (M : TM n) := loop (@step _ M) (@haltConf _ M).
  
  (* Initial configuration *)  
  Definition initc n (M : TM n) tapes :=
    mk_mconfig (n := n) (@start _ n M) tapes.

  (* *** Realisation *)

  (* Parametrised relations *)
  Definition pRel (sig : Type) (F: Type) (n : nat) := Rel (tapes sig n) (F * tapes sig n).

  (* A (labelled) machine [M] realises a (labelled) relation [R], if: for every tape vectors [t], if [M] with [t] terminates in a configuration [c], then [R (t), (projT2 M (cstate c), ctapes c)]. That means that the pair of the input tape vectors, the labelof the state in that the machine terminated, and the output tape, must be in the relation [R]. *)
  
  Definition Realise n F (pM : pTM n F) (R : pRel sig n F) :=
    forall t k outc, loopM (initc (projT1 pM) t) k = Some outc -> R t (projT2 pM (cstate outc), ctapes outc).

  Notation "M '⊨' R" := (Realise M R) (no associativity, at level 30, format "M  '⊨'  R").

  (* Realisation is monotone *)
  Lemma Realise_monotone n (F : Type) (pM : pTM F n) R R' :
    pM ⊨ R' -> R' <<=2 R -> pM ⊨ R.
  Proof. firstorder. Qed.


  (* *** Termination/Runtime *)

  (* A machine is said to "terminate in" a relation [T : Rel (tapes sig n) nat], if for every pair of input tape vectors [t] and step numbers [k] such that T t k, there exists an output configuration [cout] that [M] reaches from [t] in [k] steps. *)

  Definition tRel sig n := Rel (tapes sig n) nat.

  Definition TerminatesIn {n : nat} (M : TM n) (T : tRel sig n) :=
    forall tin k, T tin k -> exists conf, loopM (initc M tin) k = Some conf.
  

  Arguments TerminatesIn { _ } _.
  Notation "M ↓ T" := (TerminatesIn M T) (no associativity, at level 60, format "M  '↓'  T").

  (* Termination is anti-monotone *)
  Lemma TerminatesIn_monotone {n : nat} (M : TM n) (T T' : tRel sig n) :
    M ↓ T' -> (T <<=2 T') -> M ↓ T.
  Proof. intros H1 H2. firstorder. Qed.

  Lemma TerminatesIn_extend {n : nat} (M : TM n) (T : tRel sig n) :
    M ↓ T ->
    M ↓ (fun tin k => exists k', k' <= k /\ T tin k').
  Proof.
    intros HTerm. hnf in *. intros tin k. intros (k'&Hk'&HT).
    specialize HTerm with (1 := HT) as (oconf&HLoop).
    exists oconf. eapply loop_monotone; eauto.
  Qed.
  

  (* Realisation plus termination in constant time *)
  Definition RealiseIn n (F : Type) (pM : pTM F n) (R : pRel sig F n) (k : nat) :=
    forall input, exists outc, loopM (initc (projT1 pM) input) k = Some outc /\ R input ((projT2 pM (cstate outc)), ctapes outc).
  Notation "M '⊨c(' k ')' R" := (RealiseIn M R k) (no associativity, at level 45, format "M  '⊨c(' k ')'  R").

  Lemma RealiseIn_monotone n (F : Type) (pM : pTM F n) (R R' : pRel sig F n) k k' :
    pM ⊨c(k') R' -> k' <= k -> R' <<=2 R -> pM ⊨c(k) R.
  Proof.
    unfold RealiseIn. intros H1 H2 H3 input.
    specialize (H1 input) as (outc & H1). exists outc.
    split.
    - unfold loopM. eapply loop_monotone; eauto. intuition.
    - intuition.
  Qed.

  Lemma RealiseIn_monotone' n (F : Type) (pM : pTM F n) (R : pRel sig F n) k k' :
    pM ⊨c(k') R -> k' <= k -> pM ⊨c(k) R.
  Proof.
    intros H1 H2. eapply RealiseIn_monotone. eapply H1. assumption. firstorder.
  Qed.

  Lemma RealiseIn_split n (F : Type) (pM : pTM F n) R1 R2 (k : nat) :
    pM ⊨c(k) R1 /\ pM ⊨c(k) R2 <-> pM ⊨c(k) R1 ∩ R2.
  Proof.
    split; swap 1 2; [ intros H | intros (H1&H2)]; repeat intros ?. hnf; firstorder eauto.
    specialize (H1 input) as (outc &H1&H1'). specialize (H2 input) as (outc2&H2&H2').
    pose proof loop_injective H1 H2 as <-. exists outc. split; hnf; eauto.
  Qed.
  
  Lemma Realise_total n (F : Type) (pM : { M : TM n & state M -> F }) R k :
    pM ⊨ R /\ projT1 pM ↓ (fun _ i => k <= i) <-> pM ⊨c(k) R.
  Proof.
    split.
    - intros (HR & Ht) t. edestruct (Ht t k). cbn; lia. eauto.
    - intros H.
      split.
      + intros t i cout Hc.
        destruct (H t) as (? & ? & ?).
        replace cout with x.
        eassumption.
        unfold loopM in *.
        eapply loop_injective; eauto.
      + intros t i Hi.
        edestruct (H t) as (? & ? & ?). 
        exists x. eapply loop_monotone; eauto.
  Qed.

  Lemma RealiseIn_Realise n (F : Type) (pM : pTM F n) R k :
    pM ⊨c(k) R -> pM ⊨ R.
  Proof. now intros (?&?) % Realise_total. Qed.

  Lemma RealiseIn_TerminatesIn n (F : Type) (pM : { M : TM n & state M -> F }) R k :
    pM ⊨c(k) R -> projT1 pM ↓ (fun tin l => k <= l). 
  Proof.
    intros HRel. hnf. intros tin l HSteps. hnf in HRel. specialize (HRel tin) as (outc&HLoop&Rloop).
    exists outc. eapply loop_monotone; eauto.
  Qed.
  
  Lemma Realise_strengthen n (F : Type) (pM : pTM F n) R1 R2 :
    Realise pM R2 -> Realise pM R1 -> Realise pM (R1 ∩ R2).
  Proof.
    intros HwR HR t. firstorder.
  Qed.


  (* *** Canonical relations *)

  Section Canonical_Correctness.
    Variable (n : nat).
    Variable (F : Type).
    Variable (pM : pTM F n).

    Definition Canonical_Rel : pRel sig F n :=
      fun t1 '(y, t2) =>
        exists outc k, loopM (M := projT1 pM) (initc (projT1 pM) t1) k = Some outc /\
                  ctapes outc = t2 /\ projT2 pM (cstate outc) = y.

    Fact Canonical_Realise :
      pM ⊨ Canonical_Rel.
    Proof. hnf. firstorder eauto. Qed.

    Lemma R_canonical_functional : functional Canonical_Rel.
    Proof.
      hnf. intros x (y1&z1) (y2&z2) (c1&k1&H1&<-&H1') (c2&k2&H2&<-&H2').
      pose proof loop_injective H1 H2 as ->. congruence.
    Qed.

  End Canonical_Correctness.

  Section Canonical_Termination.
    Variable (n : nat).
    Variable (M : TM n).

    Definition Canonical_T : tRel sig n :=
      fun t k => exists outc, loopM (M := M) (initc M t) k = Some outc.

    Lemma Canonical_TerminatesIn :
      M ↓ Canonical_T.
    Proof. firstorder. Qed.

  End Canonical_Termination.


End Semantics.



(* Notation for parametrised Turing machines *)
Notation "'(' M ';' labelling ')'" := (existT (fun x => state x -> _) M labelling).

(* Notations for semantic of concrete Turing machines *)
Notation "M '⊨' R" := (Realise M R) (no associativity, at level 60, format "M  '⊨'  R").
Notation "M '⊨c(' k ')' R" := (RealiseIn M R k) (no associativity, at level 45, format "M  '⊨c(' k ')'  R").
Notation "M '↓' t" := (TerminatesIn M t) (no associativity, at level 60, format "M  '↓'  t").



(* [inhabitedC] instances for state and labels *)

#[global]
Instance inhabited_move : inhabitedC move := ltac:(repeat constructor).

#[global]
Instance inhabited_TM_Q (n : nat) (sig : finType) (M : TM sig n) : inhabitedC (state M).
Proof. constructor. apply start. Qed.

Lemma inhabited_pTM_lab (n : nat) (sig : finType) (F : Type) (pM : pTM sig F n) : inhabitedC F.
Proof. constructor. apply (projT2 pM). apply default. Qed.

#[export] Hint Extern 4 => once lazymatch goal with
                | [ pM : pTM ?sig ?F ?n |- inhabitedC ?F ] => apply (inhabited_pTM_lab pM)
                end : typeclass_instances.

Section Test_def.
  Variable (n : nat) (sig : finType) (F : Type).
  Variable (pM : pTM sig F n).
  Goal let _ := default : state (projT1 pM) in True. Proof. exact I. Qed.  
  Goal let _ :=  default : F in True. Proof. exact I. Qed.  
End Test_def.




(* Auxiliary function to actually execute a machine *)
Definition execTM (sig : finType) (n : nat) (M : TM sig n) (tapes : tapes sig n) (k : nat) :=
  option_map (@ctapes _ _ _) (loopM (initc M tapes) k).

Definition execTM_p (sig : finType) (n : nat) (F : Type) (pM : { M : TM sig n & state M -> F }) (tapes : tapes sig n) (k : nat) :=
  option_map (fun x => (ctapes x, projT2 pM (cstate x))) (loopM (initc (projT1 pM) tapes) k ).



(* ** Automation of the generation of relations *)

(* Create the smpl tactic databases *)
Smpl Create TM_Correct.

(* This tactics apply exactly one tactic from the corresponding hint database *)
Ltac TM_Correct_step := smpl TM_Correct.
Ltac TM_Correct := repeat TM_Correct_step.

(* ** TM evaluation and loop is equivalent  *)

Lemma Vector_map2_ext {A B C} (f g : A -> B -> C) n (v1 : Vector.t A n) (v2 : Vector.t B n) :
  (forall a b, f a b = g a b) ->
  Vector.map2 f v1 v2 = Vector.map2 g v1 v2.
Proof.
  intros H.
  pattern n, v1, v2; revert n v1 v2.
  eapply Vector.rect2.
  - reflexivity.
  - intros n v1 v2 IH a b. cbn. now rewrite H, IH.
Qed.

Lemma TM_eval_iff (Σ : finType) n (M : TM Σ n) q t q' t' :
  TM.eval M q t q' t' <-> exists n, loopM (M := M) (mk_mconfig q t) n = Some (mk_mconfig q' t').
Proof.
  split.
  - induction 1 as [ | q t q' a q'' t' H0 H1 H2 [m IH]].
    + exists 0. cbn. unfold haltConf. cbn. now rewrite H.
    + exists (S m). cbn. unfold haltConf. cbn. rewrite H0.
      unfold step. cbn. unfold current_chars.
      rewrite H1. erewrite Vector_map2_ext.
      * now rewrite IH.
      * intros [] [[] []]; reflexivity.
  - intros [k H].
    induction k in q, t, H, q', t' |- *; cbn in H; unfold haltConf in H; cbn in H.
    + destruct halt eqn:E; inv H. now econstructor.
    + destruct halt eqn:E; inv H.
      * now econstructor.
      * unfold step in H1. cbn in H1.
        destruct trans eqn:E2.
        econstructor; [ eassumption .. | ].
        eapply IHk. erewrite Vector_map2_ext.
        -- now rewrite H1.
        -- intros [] [[] []]; reflexivity.
Qed.

