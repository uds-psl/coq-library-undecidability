(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(* Require Import Arith Omega Max List. *)

Require Import Arith Omega List Permutation.
Require Import utils pos.

Set Implicit Arguments.

Section vector.

  Variable X : Type.

  Inductive vec : nat -> Type :=
    | vec_nil  : vec 0
    | vec_cons : forall n, X -> vec n -> vec (S n).

  Let vec_split_type n := 
    match n with
      | 0   => Prop
      | S n => (X * vec n)%type
    end.

  Definition vec_split n (v : vec n) : vec_split_type n :=
    match v in vec k return vec_split_type k with
      | vec_nil  => False
      | @vec_cons n x v => (x,v)
    end.
    
  Definition vec_head n (v : vec (S n)) := match v with @vec_cons _ x _ => x end.
  Definition vec_tail n (v : vec (S n)) := match v with @vec_cons _ _ w => w end.

  Let vec_head_tail_type n : vec n -> Prop := 
    match n with
      | 0   => fun v => v = vec_nil
      | S n => fun v => v = vec_cons (vec_head v) (vec_tail v)
    end.

  Let vec_head_tail_prop n v :  @vec_head_tail_type n v.
  Proof. induction v; simpl; auto. Qed.

  Fact vec_0_nil (v : vec 0) : v = vec_nil.
  Proof. apply (vec_head_tail_prop v). Qed.

  Fact vec_head_tail n (v : vec (S n)) : v = vec_cons (vec_head v) (vec_tail v).
  Proof. apply (vec_head_tail_prop v). Qed.

  Fixpoint vec_pos n (v : vec n) : pos n -> X.
  Proof.
    refine (match v with
      | vec_nil => fun p => _
      | @vec_cons n x v => fun p => _
    end); invert pos p.
    exact x.
    exact (vec_pos _ v p).
  Defined.

  Fact vec_pos0 n (v : vec (S n)) : vec_pos v pos0 = vec_head v.
  Proof. 
    rewrite (vec_head_tail v).
    reflexivity.
  Qed.
  
  Fact vec_pos_tail n (v : vec (S n)) p : vec_pos (vec_tail v) p = vec_pos v (pos_nxt p).
  Proof.
    rewrite vec_head_tail at 2; simpl; auto.
  Qed.
  
  Fact vec_pos1 n (v : vec (S (S n))) : vec_pos v pos1 = vec_head (vec_tail v).
  Proof.
    rewrite <- vec_pos0, vec_pos_tail; auto.
  Qed.

  Fact vec_pos_ext n (v w : vec n) : (forall p, vec_pos v p = vec_pos w p) -> v = w.
  Proof.
    revert v w; induction n as [ | n IHn ]; intros v w H.
    rewrite (vec_0_nil v), (vec_0_nil w); auto.
    revert H; rewrite (vec_head_tail v), (vec_head_tail w); f_equal.
    intros H; f_equal.
    apply (H pos0).
    apply IHn.
    intros p; apply (H (pos_nxt p)).
  Qed.

  Fixpoint vec_set_pos n : (pos n -> X) -> vec n :=
    match n return (pos n -> X) -> vec n with 
      | 0   => fun _ => vec_nil
      | S n => fun g => vec_cons (g pos0) (vec_set_pos (fun p => g (pos_nxt p)))
    end.

  Fact vec_pos_set n (g : pos n -> X) p : vec_pos (vec_set_pos g) p = g p. 
  Proof.
    revert g p; induction n as [ | n IHn ]; intros g p; pos_inv p; auto.
    apply IHn.
  Qed.

  Fixpoint vec_change n (v : vec n) : pos n -> X -> vec n.
  Proof.
    refine (match v with
      | vec_nil         => fun _ _ => vec_nil
      | @vec_cons n y v => fun p x => _
    end).
    pos_inv p.
    exact (vec_cons x v).
    apply (vec_cons y), (vec_change _ v p x).
  Defined.

  Fact vec_change_eq n v p q x : p = q -> vec_pos (@vec_change n v p x) q = x.
  Proof. 
    intro; subst q; revert p x.
    induction v; intros p ?; invert pos p; auto.
  Qed.

  Fact vec_change_neq n v p q x : p <> q -> vec_pos (@vec_change n v p x) q = vec_pos v q.
  Proof. 
    revert p q x.
    induction v as [ | n y v IH ]; intros p q x H; invert pos p; invert pos q; auto.
    destruct H; auto.
    apply IH; contradict H; subst; auto.
  Qed.

  Fact vec_change_idem n v p x y : vec_change (@vec_change n v p x) p y = vec_change v p y.
  Proof.
    apply vec_pos_ext; intros q.
    destruct (pos_eq_dec p q).
    repeat rewrite vec_change_eq; auto.
    repeat rewrite vec_change_neq; auto.
  Qed.

  Fact vec_change_same n v p : @vec_change n v p (vec_pos v p) = v.
  Proof.
    apply vec_pos_ext; intros q.
    destruct (pos_eq_dec p q).
    repeat rewrite vec_change_eq; subst; auto.
    repeat rewrite vec_change_neq; auto.
  Qed.

  Variable eq_X_dec : forall x y : X, { x = y } + { x <> y }.

  Fixpoint vec_eq_dec n (u v : vec n) : { u = v } + { u <> v }.
  Proof.
    destruct u as [ | n x u ].
    left.
    rewrite vec_0_nil; trivial.
    destruct (eq_X_dec x (vec_head v)) as [ E1 | D ].
    destruct (vec_eq_dec _ u (vec_tail v)) as [ E2 | D ].
    left; subst; rewrite <- vec_head_tail; auto.
    right; contradict D; subst; rewrite <- D; auto.
    right; contradict D; subst; auto.
  Defined.
  
  Fixpoint vec_list n (v : vec n) := 
    match v with  
      | vec_nil      => nil
      | vec_cons x v => x::vec_list v
    end.
    
  Fact vec_list_length n v : length (@vec_list n v) = n.
  Proof. induction v; simpl; f_equal; auto. Qed.

  Fact vec_list_inv n v x : In x (@vec_list n v) -> exists p, x = vec_pos v p.
  Proof.
    induction v as [ | n y v IHl ].
    intros [].
    intros [ H | H ]; subst.
    exists pos0; auto.
    destruct IHl as (p & Hp); auto.
    subst; exists (pos_nxt p); auto.
  Qed.

End vector.

(* notations *)

Arguments vec_nil { X }.

Infix "##" := vec_cons (at level 60, right associativity).

Fixpoint vec_map X Y (f : X -> Y) n (v : vec X n) :=
  match v with 
    | vec_nil => vec_nil
    | x ## v  => f x ## vec_map f v 
  end.

Fact vec_pos_map X Y (f : X -> Y) n (v : vec X n) p : vec_pos (vec_map f v) p = f (vec_pos v p).
Proof.
  revert p; induction v; intros p; pos_inv p; simpl; auto.
Qed.

  
Section vec_plus.

  Variable n : nat.

  Definition vec_plus (v w : vec nat n) := vec_set_pos (fun p => vec_pos v p + vec_pos w p).
  Definition vec_zero : vec nat n := vec_set_pos (fun _ => 0).
  
  Fact vec_pos_plus v w p : vec_pos (vec_plus v w) p = vec_pos v p + vec_pos w p.
  Proof.
    unfold vec_plus; rewrite vec_pos_set; auto.
  Qed.

  Fact vec_zero_plus v : vec_plus vec_zero v = v.
  Proof. 
    apply vec_pos_ext.
    intros p; unfold vec_zero, vec_plus. 
    repeat rewrite vec_pos_set; auto.
  Qed.
  
  Fact vec_zero_spec p : vec_pos vec_zero p = 0.
  Proof. unfold vec_zero; rewrite vec_pos_set; trivial. Qed.

  Fact vec_plus_comm v w : vec_plus v w = vec_plus w v.
  Proof.
    apply vec_pos_ext.
    intros p; unfold vec_zero, vec_plus.
    repeat rewrite vec_pos_set; omega.
  Qed.

  Fact vec_plus_assoc u v w : vec_plus u (vec_plus v w) = vec_plus (vec_plus u v) w.
  Proof.
    apply vec_pos_ext.
    intros p; unfold vec_zero, vec_plus.
    repeat rewrite vec_pos_set; omega.
  Qed.

  Fact vec_plus_is_zero u v : vec_zero = vec_plus u v -> u = vec_zero /\ v = vec_zero.
  Proof.
   unfold vec_zero, vec_plus; intros H; split; apply vec_pos_ext;
   intros p; apply f_equal with (f := fun v => vec_pos v p) in H;
   repeat rewrite vec_pos_set in * |- *; omega.
  Qed.
  
  Definition vec_one p : vec _ n := vec_set_pos (fun q => if pos_eq_dec p q then 1 else 0).
  
  Fact vec_one_spec_eq p q : p = q -> vec_pos (vec_one p) q = 1.
  Proof.
    intros [].
    unfold vec_one; rewrite vec_pos_set.
    destruct (pos_eq_dec p p) as [ | [] ]; auto.
  Qed.
  
  Fact vec_one_spec_neq p q : p <> q -> vec_pos (vec_one p) q = 0.
  Proof.
    intros H.
    unfold vec_one; rewrite vec_pos_set.
    destruct (pos_eq_dec p q) as [ | ]; auto.
    destruct H; auto.
  Qed.
  
End vec_plus.

Arguments vec_plus {n}.
Arguments vec_zero {n}.
Arguments vec_one {n}.

Reserved Notation " e '#>' x " (at level 58).
Reserved Notation " e [ v / x ] " (at level 57, v at level 0, x at level 0, left associativity).

Local Notation " e '#>' x " := (vec_pos e x) (at level 58).
Local Notation " e [ v / x ] " := (vec_change e x v) (at level 57, v at level 0, x at level 0, left associativity).

Tactic Notation "rew" "vec" :=
  repeat lazymatch goal with 
    |              |- context[ _[_/?x]#>?x ] => rewrite vec_change_eq with (p := x) (1 := eq_refl)
    | _ : ?x = ?y  |- context[ _[_/?x]#>?y ] => rewrite vec_change_eq with (p := x) (q := y)
    | _ : ?y = ?x  |- context[ _[_/?x]#>?y ] => rewrite vec_change_eq with (p := x) (q := y)
    | _ : ?x <> ?y |- context[ _[_/?x]#>?y ] => rewrite vec_change_neq with (p := x) (q := y)
    | _ : ?y <> ?x |- context[ _[_/?x]#>?y ] => rewrite vec_change_neq with (p := x) (q := y)
    |              |- context[ vec_pos vec_zero ?x ] => rewrite vec_zero_spec with (p := x)
    |              |- context[ vec_pos (vec_one ?x) ?x ] => rewrite vec_one_spec_eq with (p := x) (1 := eq_refl)
    | _ : ?x = ?y  |- context[ vec_pos (vec_one ?x) ?y ] => rewrite vec_one_spec_eq with (p := x) (q := y)
    | _ : ?y = ?x  |- context[ vec_pos (vec_one ?x) ?y ] => rewrite vec_one_spec_eq with (p := x) (q := y)
    | _ : ?x <> ?y |- context[ vec_pos (vec_one ?x) ?y ] => rewrite vec_one_spec_neq with (p := x) (q := y)
    | _ : ?y <> ?x |- context[ vec_pos (vec_one ?x) ?y ] => rewrite vec_one_spec_neq with (p := x) (q := y)
    | |- context[ _[_/?x][_/?x] ] => rewrite vec_change_idem with (p := x) 
    | |- context[ ?v[(?v#>?x)/?x] ] => rewrite vec_change_same with (p := x)
    | |- context[ _[_/?x]#>?y ] => rewrite vec_change_neq with (p := x) (q := y); [ | discriminate ]
    | |- context[ vec_plus vec_zero ?x ] => rewrite vec_zero_plus with (v := x)
    | |- context[ vec_plus ?x vec_zero ] => rewrite (vec_plus_comm x vec_zero); rewrite vec_zero_plus with (v := x)
    | |- vec_plus ?x ?y = vec_plus ?y ?x => apply vec_plus_comm
  end; auto.
  
Fact vec_zero_S n : @vec_zero (S n) = 0##vec_zero.
Proof. auto. Qed.

Fact vec_one_fst n : @vec_one (S n) pos0 = 1##vec_zero.
Proof.
  apply vec_pos_ext.
  intros p; pos_inv p; rew vec.
Qed.

Fact vec_one_nxt n p : @vec_one (S n) (pos_nxt p) = 0##vec_one p.
Proof.
  apply vec_pos_ext.
  unfold vec_one.
  intros q; rewrite vec_pos_set.
  pos_inv q.
  simpl; auto.
  rewrite <- vec_pos_tail.
  simpl vec_tail.
  rewrite vec_pos_set.
  destruct (pos_eq_dec p q) as [ | C ].
  subst.
  destruct (pos_eq_dec (pos_nxt q) (pos_nxt q)) as [ | [] ]; auto.
  destruct (pos_eq_dec (pos_nxt p) (pos_nxt q)) as [ | ]; auto.
  destruct C; apply pos_nxt_inj; auto.
Qed.

Fact vec_plus_cons n x v y w : @vec_plus (S n) (x##v) (y##w) = x+y ## vec_plus v w.
Proof.
  apply vec_pos_ext; unfold vec_plus.
  intros p; pos_inv p; repeat (rewrite vec_pos_set; simpl; auto).
Qed.

Fact vec_change_succ n v p : v[(S (v#>p))/p] = @vec_plus n (vec_one p) v.
Proof.
  apply vec_pos_ext.
  intros q.
  destruct (pos_eq_dec p q); rew vec;
  rewrite vec_pos_plus; rew vec; subst; auto.
Qed.

Fact vec_change_pred n v p u : v#>p = S u -> v = @vec_plus n (vec_one p) (v[u/p]).
Proof.
  intros Hu.
  apply vec_pos_ext.
  intros q.
  destruct (pos_eq_dec p q); rew vec;
  rewrite vec_pos_plus; rew vec; subst; auto.
Qed.

Fixpoint vec_sum n (v : vec nat n) := 
  match v with 
    | vec_nil       => 0
    | vec_cons x w  => x + vec_sum w
  end.
  
Fact vec_sum_plus n v w : @vec_sum n (vec_plus v w) = vec_sum v + vec_sum w.
Proof.
  revert w; induction v; intros w.
  rewrite (vec_0_nil (vec_plus _ _)), (vec_0_nil w); auto.
  rewrite (vec_head_tail w), vec_plus_cons; simpl.
  rewrite IHv; omega.
Qed.

Fact vec_sum_zero n : @vec_sum n vec_zero = 0.
Proof. induction n; simpl; auto. Qed.

Fact vec_sum_one n p : @vec_sum n (vec_one p) = 1.
Proof.
  revert p; induction n; intros p.
  pos_inv p.
  pos_inv p.
  rewrite vec_one_fst.
  simpl; f_equal; apply vec_sum_zero.
  rewrite vec_one_nxt.
  unfold vec_sum; fold vec_sum.
  rewrite IHn; auto.
Qed.
  
Fact vec_sum_is_zero n v : @vec_sum n v = 0 -> v = vec_zero.
Proof.
  induction v; simpl; auto.
  simpl; rewrite vec_zero_S; intros; f_equal.
  omega.
  apply IHv; omega.
Qed.

Fact vec_sum_is_nzero n v : 0 < @vec_sum n v -> { p : _ & { w | v = vec_plus (vec_one p) w } }.
Proof.
  induction v as [ | n x v IHv ]; intros Hv; simpl in Hv.
  omega.
  destruct x as [ | x ].
  apply IHv in Hv.
  destruct Hv as (p & w & Hw).
  exists (pos_nxt p), (0##w); rewrite vec_one_nxt.
  rewrite vec_plus_cons; f_equal; auto.
  exists pos0, (x##v).
  rewrite vec_one_fst, vec_plus_cons; rew vec.
Qed.

Section vec_nat_induction.

  (* Specialized induction on vec nat n, with constant n *)

  Variable (n : nat) (P : vec nat n -> Type).
  
  Hypothesis HP0 : P vec_zero.
  Hypothesis HP1 : forall p, P (vec_one p).
  Hypothesis HP2 : forall v w, P v -> P w -> P (vec_plus v w).
  
  Theorem vec_nat_induction v : P v.
  Proof.
    induction v as [ v IHv ] using (measure_rect (@vec_sum n)).
    case_eq (vec_sum v).
    
    intros Hv.
    apply vec_sum_is_zero in Hv; subst; auto.
    
    intros x Hx.
    destruct (vec_sum_is_nzero v) as (p & w & Hw).
    omega.
    subst.
    apply HP2; auto.
    apply IHv.
    rewrite vec_sum_plus, vec_sum_one; auto.
  Qed.
  
End vec_nat_induction.

Section vec_map_list.

  Variable X : Type.

  (* morphism between vec nat n and (list X)/~p *)

  Fixpoint vec_map_list X n v : (pos n -> X) -> list X :=
    match v in vec _ m return (pos m -> _) -> _ with
      | vec_nil => fun _ => nil
      | a##v    => fun f => list_repeat (f pos0) a ++ vec_map_list v (fun p => f (pos_nxt p))
    end.

  Fact vec_map_list_zero n f : vec_map_list (@vec_zero n) f = @nil X.
  Proof. revert f; induction n; intros f; simpl; auto. Qed.

  Fact vec_map_list_one n p f : vec_map_list (@vec_one n p) f = f p :: @nil X.
  Proof.
    revert f; induction p; intro.
    rewrite vec_one_fst; simpl; rewrite vec_map_list_zero; auto.
    rewrite vec_one_nxt; simpl; rewrite IHp; auto.
  Qed.

  (* The morphism *)

  Fact vec_map_list_plus n v w f : @vec_map_list X n (vec_plus v w) f ~p vec_map_list v f ++ vec_map_list w f.
  Proof.
    revert v w f; induction n as [ | n IHn ]; intros v w f.
    rewrite (vec_0_nil (vec_plus v w)), (vec_0_nil v), (vec_0_nil w); simpl; auto.
    rewrite (vec_head_tail v), (vec_head_tail w), vec_plus_cons.
    generalize (vec_head v) (vec_tail v) (vec_head w) (vec_tail w); clear v w; intros x v y w.
    simpl.
    rewrite list_repeat_plus.
    solve list eq; apply Permutation_app; auto.
    apply Permutation_trans with (list_repeat (f pos0) y 
                               ++ vec_map_list v (fun p => f (pos_nxt p)) 
                               ++ vec_map_list w (fun p => f (pos_nxt p))).
    apply Permutation_app; auto.
    do 2 rewrite <- app_ass.
    apply Permutation_app; auto.
    apply Permutation_app_comm.
  Qed.

End vec_map_list.

Fact map_vec_map_list X Y (f : X -> Y) n v g : map f (@vec_map_list _ n v g) = vec_map_list v (fun p => f (g p)).
Proof.
  revert g; induction v; intro; simpl; auto.
  rewrite map_app; f_equal; auto.
  rewrite map_list_repeat; auto.
Qed.

Definition list_vec X (l : list X) : { v : vec X (length l) | vec_list v = l }.
Proof.
  induction l as [ | x l (v & Hv) ]; simpl.
  exists vec_nil; auto.
  exists (x##v); simpl; f_equal; auto.
Qed.
