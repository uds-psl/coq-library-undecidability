Require Import Undecidability.FOLC.GenCompleteness.

(** ** WKL  *)

(** The predicate [suffix] holds if the first list is a suffix of the second.
The predicate [prefix] holds if the first list is a prefix of the second. *)
Definition prefix {A} : list A -> list A -> Prop := fun l1 l2 => exists k, l2 = l1 ++ k.
Infix "`prefix_of`" := prefix (at level 70) : stdpp_scope.

Definition decidable {X} (p : X -> Prop) := exists f, forall x, p x <-> f x = true.

Record is_tree (tree_T : list bool -> Prop) :=
  {
    tree_inhab : exists l : list bool, tree_T l ;
    tree_p : forall l1 l2, prefix l1 l2 -> tree_T l2 -> tree_T l1 ;
    tree_dec :       decidable tree_T ;
  }.

Record tree :=
  {
  tree_T :> list bool -> Prop ;
  tree_is_tree :> is_tree tree_T
  }.

Definition bounded_tree (T : list bool -> Prop) := 
  exists k, forall a, length a >= k -> ~ T a.

Definition infinite_tree (T : list bool -> Prop) := 
  forall k, exists a, T a /\ (length a >= k ).

Definition infinite_path (T : list bool -> Prop) :=
  exists f : nat -> bool, forall n, T (map f (seq 0 n)).

Definition wellfounded_tree (T : list bool -> Prop) :=
  forall f : nat -> bool, exists n, ~ T (map f (seq 0 n)).

Lemma bounded_infinite_contra T :
  bounded_tree T -> infinite_tree T -> False.
Proof.
  firstorder.
Qed. 

Lemma path_wellfounded_contra T :
  infinite_path T -> wellfounded_tree T -> False.
Proof.
  intros [f H] H2.
  specialize (H2 f) as [n].
  eauto.
Qed.

Definition WKL :=
  forall T : tree, infinite_tree T -> infinite_path T.

(** ** Model existence  *)

Definition model_existence (Cond : forall Sigma D, @interp Sigma D -> Prop) :=
  forall {Sigma : Signature},
  forall {HdF : eq_dec Funcs} {HdP : eq_dec Preds},
  forall {HeF : enumT Funcs} {HeP : enumT Preds},
  forall T (T_closed : closed_T T), consistent T ->
  exists (D : Type) (I : @interp Sigma D), inhabited (eq_dec D) /\ inhabited (enumT D) /\
                                      Cond Sigma D I /\ 
                                      forall phi, closed phi -> phi ∈ T -> forall rho, rho ⊨ phi.

Goal model_existence (@SM).
Proof.
  intros Sigma HdF HdP HeF HeP T T_closed T_cons.
  pose proof (@model_bot_correct Sigma HdF HdP HeF HeP T T_closed).
  exists (@term Sigma). eexists.
  setoid_rewrite <- H.
  repeat split; try exact _.
  - eapply model_bot_classical.
  - now eapply model_bot_standard.
  - intros. eapply Out_T_sub. cbn. 
    setoid_rewrite subst_unused_closed. 2:eauto.
    asimpl. eassumption.
Qed.

Definition DM `{Signature} D (I : interp D) := classical I /\ standard_bot I /\ GenTarski.decidable I.

(* Goal model_existence_dec -> WKL. *)
(* Proof. *)
(*   intros me T Ht. *)
(*   specialize (me (B_S False ltac:(tauto) nat (fun _ => 0)) _ _ _ _). *)
