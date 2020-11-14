(** Instance declaration for dependent pairs *)

From Undecidability.Shared.Libs.PSL Require Import Base FinTypes.
From Coq Require Import EqdepFacts List.

Instance eqType_depPair (F : eqType) (a : F -> eqType) : eq_dec {f : F & a f}.
Proof.
  intros [x fx] [y fy]. eapply dec_transfer. now rewrite eq_sigT_iff_eq_dep.
  decide (x=y).
  subst y. decide (fx = fy).
  +subst fy. left. reflexivity.
  +right. intros eq. apply n. apply Eqdep_dec.eq_dep_eq_dec in eq. auto. intros. decide (x0=y);econstructor;eassumption;eauto.
  +right. intros eq. now inv eq.
Qed.

Instance finType_depPair (F : finType) (a : F -> finType) : finTypeC (EqType( {f : F & a f} )).
Proof. 
  exists (undup (concat (map (fun f => map (fun x => existT a _ x) (elem (a f))) (elem F)))).
  intros H. hnf in H. apply dupfreeCount. now apply dupfree_undup.
  rewrite undup_id_equi. apply in_concat_iff.
  exists ((fun f : F => map (fun x : a f => existT (fun x0 : F => a x0) f x) (elem (a f))) (projT1 H)).
  split.
  -rewrite in_map_iff. destruct H. cbn. exists e. split.
   +reflexivity.
   +apply countIn. setoid_rewrite enum_ok. lia.
  -rewrite in_map_iff. eexists. split. reflexivity.
   apply countIn. setoid_rewrite enum_ok. lia. 
Qed.

Hint Extern 4 (finTypeC (EqType ({_ : _ & _}))) => eapply finType_depPair : typeclass_instances.

(* (** * Dependent pairs *) *)

(* Fixpoint toSigTList (X: Type) (f: X -> finType) (A: list X) : list (sigT f) := *)
(*   match A with *)
(*   | nil => nil *)
(*   | cons x A' => (map (existT f x) (elem (f x))) ++ toSigTList f A' end. *)


(* Lemma countMapExistT (X: eqType) (f: X -> eqType) (x:X) (A: list (f x)) (y: f x) : *)
(*   count (map (existT f x) A) (existT f x y) = count A y. *)
(* Proof. *)
(*   induction A. *)
(*   -  reflexivity. *)
(*   - simpl. dec. *)
(*     + subst a. f_equal. apply IHA. *)
(*     + contradict n. exact (sigT_proj2_fun _ e). *)
(*     + subst a. contradict n. reflexivity. *)
(*     + exact IHA. *)
(* Qed.       *)

(* Lemma countMapExistT_Zero (X: eqType) (f: X -> eqType) (x x':X) (A: list (f x)) (y: f x') : *)
(*   x <> x' -> count (map (existT f x) A) (existT f x' y) = 0. *)
(* Proof. *)
(*   intros E. induction A. *)
(*   - reflexivity. *)
(*   - simpl. dec. *)
(*     + contradict E. eapply sigT_proj1_fun; eauto. *)
(*     + exact IHA. *)
(* Qed. *)

(* Lemma toSigTList_count (X: eqType) (f: X -> finType) (A: list X) (s: sigT f): *)
(*   count (toSigTList f A) s = count A (projT1 s). *)
(* Proof. *)
(*   induction A. *)
(*   - reflexivity. *)
(*   -  destruct s. cbn in *. rewrite <- countSplit. rewrite IHA. dec. *)
(*     + change (S (count A x)) with (1 + count A x). f_equal. subst a. *)
(*       rewrite (@countMapExistT _ f x (elem (f x)) e). apply enum_ok. *)
(*     + change (count A x) with (0+ (count A x)). f_equal. rewrite (@countMapExistT_Zero _ f a x); auto. *)
(* Qed. *)

(* Lemma sigT_enum_ok (X:finType) (f: X -> finType) (s: sigT f) : count (toSigTList f (elem X)) s = 1. *)
(* Proof. *)
(*   rewrite toSigTList_count. now pose proof (enum_ok (projT1 s)). *)
(* Qed. *)

(* Instance finTypeC_sigT (X: finType) (f: X -> finType): finTypeC (EqSigT f). *)
(* Proof. *)
(*   econstructor.  apply sigT_enum_ok. *)
(* Defined. *)

(* Canonical Structure finType_sigT (X: finType) (f: X -> finType) := FinType (EqSigT f). *)

(* Lemma finType_sigT_correct (X: finType) (f: X -> finType): *)
(*   sigT f = finType_sigT f. *)
(* Proof. *)
(*   reflexivity. *)
(* Qed. *)

(* Lemma finType_sigT_enum (X: finType) (f: X -> finType) : *)
(*   toSigTList f (elem X) = (elem (finType_sigT f)). *)
(* Proof. *)
(*   reflexivity. *)
(* Qed. *)
(* Set Printing Coercions. *)
(* Lemma tofinType_sigT_correct (X: finType) (f: X -> finType) : *)
(*   tofinType (sigT f) = finType_sigT f. *)
(* Proof. *)
(*   reflexivity. *)
(* Qed. *)
(* Unset Printing Coercions. *)
