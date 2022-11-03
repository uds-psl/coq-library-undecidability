From Undecidability.Shared.Libs.PSL Require Export Prelim EqDec.

Export List.ListNotations.
Notation "x 'el' A" := (In x A) (at level 70).
Notation "A <<= B" := (incl A B) (at level 70).
Notation "| A |" := (length A) (at level 65).

#[export] Hint Extern 4 => 
match goal with
|[ H: ?x el nil |- _ ] => destruct H
end : core.

(* ** Lists *)

(* *** Duplicate-free lists *)
Notation dupfree := List.NoDup.

Definition undup {X : eqType} (A : list X) : list X :=
  nodup (@eqType_dec X) A.

Create HintDb list.

(* Register additional simplification rules with autorewrite / simpl_list *)
(* Print Rewrite HintDb list. *)
Global Hint Rewrite <- app_assoc : list.
Global Hint Rewrite rev_app_distr map_app prod_length : list.

(* *** Decisions for lists *)

#[global]
Instance list_in_dec X (x : X) (A : list X) :  
  eq_dec X -> dec (x el A).
Proof.
  intros D. apply in_dec. exact D.
Qed.

(* Certifying find *)

Lemma cfind X A (p: X -> Prop) (p_dec: forall x, dec (p x)) :
  {x | x el A /\ p x} + {forall x, x el A -> ~ p x}.
Proof.
  destruct (find (fun x => Dec (p x)) A) eqn:E.
  - apply find_some in E. firstorder.
  - right. intros. eapply find_none in E; eauto.
Qed.

Arguments cfind {X} A p {p_dec}.

#[export]
Instance list_forall_dec X A (p : X -> Prop) :
  (forall x, dec (p x)) -> dec (forall x, x el A -> p x).
Proof.
  intros p_dec.
  destruct (find (fun x => Dec (~ p x)) A) eqn:Eq.
  - apply find_some in Eq as [H1 H0 %Dec_true]; right; auto. 
  - left. intros x E. apply find_none with (x := x) in Eq. apply dec_DN; auto. auto.
Qed.

#[export]
Instance list_exists_dec X A (p : X -> Prop) :
  (forall x, dec (p x)) -> dec (exists x, x el A /\ p x).
Proof.
  intros p_dec.
  destruct (find (fun x => Dec (p x)) A) eqn:Eq. (* New: eta expansion needed *)
  - apply find_some in Eq as [H0 H1 %Dec_true]. firstorder. (* New: Need firstorder here *)
  - right. intros [x [E F]]. apply find_none with (x := x) in Eq; auto. eauto. (* New: Why can't auto solve this? *)
Qed.

Lemma list_cc X (p : X -> Prop) A : 
  (forall x, dec (p x)) -> 
  (exists x, x el A /\ p x) -> {x | x el A /\ p x}.
Proof.
  intros D E. 
  destruct (cfind A p) as [[x [F G]]|F].
  - eauto.
  - exfalso. destruct E as [x [G H]]. apply (F x); auto.
Qed.

(* *** Membership

We use the following lemmas from Coq's standard library List.
- [in_eq :  x el x::A]
- [in_nil :  ~ x el nil]
- [in_cons :  x el A -> x el y::A]
- [in_or_app :  x el A \/ x el B -> x el A++B]
- [in_app_iff :  x el A++B <-> x el A \/ x el B]
- [in_map_iff :  y el map f A <-> exists x, f x = y /\ x el A]
*)

(* TODO put into list db *)
#[export] Hint Resolve in_eq in_nil in_cons in_or_app : core.

(* *** Inclusion

We use the following lemmas from Coq's standard library List.
- [incl_refl :  A <<= A]
- [incl_tl :  A <<= B -> A <<= x::B]
- [incl_cons : x el B -> A <<= B -> x::A <<= B]
- [incl_appl : A <<= B -> A <<= B++C]
- [incl_appr : A <<= C -> A <<= B++C]
- [incl_app : A <<= C -> B <<= C -> A++B <<= C]
*)

#[export] Hint Resolve incl_refl incl_tl incl_cons incl_appl incl_appr incl_app incl_nil_l : core.

Lemma app_comm_cons' (A : Type) (x y : list A) (a : A) :
  x ++ a :: y = (x ++ [a]) ++ y.
Proof. rewrite <- app_assoc. cbn. trivial. Qed.


(* skipn *)

Lemma skipn_app (X : Type) (xs ys : list X) (n : nat) :
  n = (| xs |) ->
  skipn n (xs ++ ys) = ys.
Proof.
  intros ->. revert ys. induction xs; cbn; auto.
Qed.

(* Injectivity of [map], if the function is injective *)
Lemma map_injective (X Y: Type) (f: X -> Y) :
  (forall x y, f x = f y -> x = y) ->
  forall xs ys, map f xs = map f ys -> xs = ys.
Proof.
  intros HInj. hnf. intros x1. induction x1 as [ | x x1' IH]; cbn in *.
  - now intros [|??].
  - intros [|??]; [easy|]. intros [= E1%HInj E2%IH]. now subst.
Qed.

(* Analogous to [removelast_app] *)

Lemma tl_app (A: Type) (xs ys : list A) :
  xs <> nil ->
  tl (xs ++ ys) = tl xs ++ ys.
Proof. destruct xs; cbn; congruence. Qed.
