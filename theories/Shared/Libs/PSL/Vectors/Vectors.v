(* * Addendum for Vectors ([Vector.t]) *)
(* Author: Maximilian Wuttke *)


From Undecidability.Shared.Libs.PSL Require Import Prelim Tactics.Tactics EqDec.
From Coq.Vectors Require Import Fin Vector.
From Undecidability.Shared.Libs.PSL Require Import Vectors.FinNotation.
From Undecidability.Shared.Libs.PSL Require Export Vectors.Fin.


(* Vector.nth should not reduce with simpl, except the index is given with a constructor *)
Arguments Vector.nth {A} {m} (v') !p.
Arguments Vector.map {A B} f {n} !v /.
Arguments Vector.map2 {A B C} g {n} !v1 !v2 /.

Tactic Notation "dependent" "destruct" constr(V) :=
  match type of V with
  | Vector.t ?Z (S ?n) =>
    revert all except V;
    pattern V; revert n V;
    eapply caseS; intros
  | Vector.t ?Z 0 =>
    revert all except V;
    pattern V; revert V;
    eapply case0; intros
  | Fin.t 0 => inv V
  | Fin.t (S ?n) =>
    let pos := V in
    revert all except pos;
    pattern pos; revert n pos;
    eapply Fin.caseS; intros
  | _ => fail "Wrong type"
  end.

Delimit Scope vector_scope with vector.
Local Open Scope vector.

Module VectorNotations2.

Notation "[ | | ]" := (nil _) (format "[ |  | ]"): vector_scope.
Notation "h ':::' t" := (cons _ h _ t) (at level 60, right associativity) : vector_scope.

Notation "[ | x | ]" := (x ::: [| |]) : vector_scope.
Notation "[ | x ; y ; .. ; z | ] " := (cons _ x _ (cons _ y _ .. (cons _ z _ (nil _)) ..))
   (format "[ | x ;  y ;  .. ;  z | ] ") : vector_scope.
Notation "v [@ p ]" := (nth v p) (at level 1, format "v [@ p ]") : vector_scope.

End VectorNotations2.

Import VectorNotations2.



Ltac existT_eq :=
  match goal with
  | [ H: existT ?X1 ?Y1 ?Z1 = existT ?X2 ?Y2 ?Z2 |- _] =>
    apply EqdepFacts.eq_sigT_iff_eq_dep in H; inv H
  end.

Ltac existT_eq' :=
  match goal with
  | [ H: existT ?X1 ?Y1 ?Z1 = existT ?X2 ?Y2 ?Z2 |- _] =>
    apply EqdepFacts.eq_sigT_iff_eq_dep in H; induction H
  end.


Lemma vect_map_injective X Y n (f : X -> Y) (v1 v2 : Vector.t X n) :
  (forall x y, f x = f y -> x = y) ->
  map f v1 = map f v2 -> v1 = v2.
Proof.
  intros Inj Eq.
  induction n; cbn in *.
  - dependent destruct v1. dependent destruct v2; reflexivity.
  - dependent destruct v1. dependent destruct v2. cbn in *.
    eapply cons_inj in Eq as (-> % Inj &?). f_equal. now apply IHn.
Qed.



Lemma replace_nth X n (v : Vector.t X n) i (x : X) :
  (Vector.replace v i x) [@i] = x.
Proof.
  induction i; dependent destruct v; cbn; auto.
Qed.

Lemma replace_nth2 X n (v : Vector.t X n) i j (x : X) :
  i <> j -> (Vector.replace v i x) [@j] = v[@j].
Proof.
  revert v. pattern i, j. revert n i j.
  eapply Fin.rect2; intros; try congruence.
  - revert f H. pattern v. revert n v.
    eapply Vector.caseS. 
    cbn. reflexivity.
  - revert f H. pattern v. revert n v.
    eapply Vector.caseS. 
    cbn. reflexivity.
  - revert g f H H0. pattern v. revert n v.
    eapply Vector.caseS. firstorder congruence.
Qed.

Lemma destruct_vector_nil (X : Type) :
  forall v : Vector.t X 0, v = [| |].
Proof.
  now apply case0.
Qed.

Lemma destruct_vector_cons (X : Type) (n : nat) :
  forall v : Vector.t X (S n), { h : X & { v' : Vector.t X n | v = h ::: v' }}.
Proof.
  revert n. apply caseS. eauto.
Qed.


Lemma In_nil (X : Type) (x : X) :
  ~ In x [| |].
Proof. intros H. inv H. Qed.

Lemma In_cons (X : Type) (n : nat) (x y : X) (xs : Vector.t X n) :
  In y (x ::: xs) -> x = y \/ In y xs.
Proof.
  intros H. inv H; existT_eq'; tauto.
Qed.

Ltac destruct_vector_in :=
  lazymatch goal with
  | [ H: Vector.In _ [| |] |- _ ] => solve [exfalso;simple apply In_nil in H;exact H]
  | [ H: Vector.In _ (?x ::: _) |- _ ] => simple apply In_cons in H as [H| H] ; try (is_var x;move H at bottom;subst x) 
  end.

(*
Goal ~ Vector.In 10 [|1;2;4|].
Proof.
  intros H. repeat destruct_vector_in; congruence.
Qed.
*)


Section In_Dec.
  Variable X : Type.
  Hypothesis X_dec : eq_dec X.

  Fixpoint in_dec (n : nat) (x : X) (xs : Vector.t X n) { struct xs } : bool :=
    match xs with
    | [| |] => false
    | y ::: xs' => if Dec (x = y) then true else in_dec x xs'
    end.

  Lemma in_dec_correct (n : nat) (x : X) (xs : Vector.t X n) :
    in_dec x xs = true <-> In x xs.
  Proof.
    split; intros.
    {
      induction xs; cbn in *.
      - congruence.
      - decide (x = h) as [ -> | D].
        + constructor.
        + constructor. now apply IHxs.
    }
    {
      induction H; cbn.
      - have (x = x).
      - decide (x = x0).
        + reflexivity.
        + apply IHIn.
    }
  Qed.

  Global Instance In_dec (n : nat) (x : X) (xs : Vector.t X n) : dec (In x xs).
  Proof. eapply dec_transfer. eapply in_dec_correct. auto. Defined.

End In_Dec.

  

(* Destruct a vector of known size *)
Ltac destruct_vector :=
  repeat match goal with
         | [ v : Vector.t ?X 0 |- _ ] =>
           let H  := fresh "Hvect" in
           pose proof (@destruct_vector_nil X v) as H;
           subst v
         | [ v : Vector.t ?X (S ?n) |- _ ] =>
           let h  := fresh "h" in
           let v' := fresh "v'" in
           let H  := fresh "Hvect" in
           pose proof (@destruct_vector_cons X n v) as (h&v'&H);
           subst v; rename v' into v
         end.



Section In_nth.
  Variable (A : Type) (n : nat).

  Lemma vect_nth_In (v : Vector.t A n) (i : Fin.t n) (x : A) :
    Vector.nth v i = x -> Vector.In x v.
  Proof.
    induction n; cbn in *.
    - inv i.
    - dependent destruct v. dependent destruct i; cbn in *; subst; econstructor; eauto.
  Qed.

  Lemma vect_nth_In' (v : Vector.t A n) (x : A) :
    Vector.In x v -> exists i : Fin.t n, Vector.nth v i = x.
  Proof.
    induction n; cbn in *.
    - inversion 1.
    - dependent destruct v. destruct_vector_in.
      + exists Fin.F1. auto.
      + specialize (IHn0 _ H) as (i&<-). exists (Fin.FS i). auto.
  Qed.

End In_nth.



Section tabulate_vec.
  Variable X : Type.

  Fixpoint tabulate (n : nat) (f : Fin.t n -> X) {struct n} : Vector.t X n.
  Proof.
    destruct n.
    - apply Vector.nil.
    - apply Vector.cons.
      + apply f, Fin.F1.
      + apply tabulate. intros m. apply f, Fin.FS, m.
  Defined.

  Lemma nth_tabulate n (f : Fin.t n -> X) (m : Fin.t n) :
    Vector.nth (tabulate f) m = f m.
  Proof.
    induction m.
    - cbn. reflexivity.
    - cbn. rewrite IHm. reflexivity.
  Qed.

  Lemma in_tabulate n (f : Fin.t n -> X) (x : X) :
    In x (tabulate (n := n) f) <-> exists i : Fin.t n, x = f i.
  Proof.
    split.
    {
      revert f x. induction n; intros f x H.
      - cbn in *. inv H.
      - cbn in *. apply In_cons in H as [ <- | H ].
        + eauto.
        + specialize (IHn (fun m => f (Fin.FS m)) _ H) as (i&IH). eauto.
    }
    {
      intros (i&Hi). induction i; cbn in *; subst; econstructor; eauto.
    }
  Qed.

  Lemma Vector_tabulate_const {n} (c : X) f :
  (forall n, f n = c) ->
  tabulate f = Vector.const c n.
  Proof.
  induction n; cbn.
  - reflexivity.
  - intros. rewrite H. f_equal. eapply IHn. intros. eapply H.
  Qed.

End tabulate_vec.

    

Lemma Vector_map_tabulate {X Y n} (f : X -> Y) g :
  Vector.map (n:=n) f (tabulate g) = tabulate (fun x => f (g x)).
Proof.
induction n; cbn.
- reflexivity.
- f_equal. eapply IHn.
Qed.


Lemma const_at n X (c : X) i :
  (Vector.const c n)[@i] = c.
Proof.
  induction i; cbn; eauto.
Qed.


(*
Lemma vec_replace_nth X x n (t : Vector.t X n) (i : Fin.t n) :
  x = Vector.nth (Vector.replace t i x) i.
Proof.
  induction i; dependent destruct t; simpl; auto.
Qed.

Lemma vec_replace_nth_nochange X x n (t : Vector.t X n) (i j : Fin.t n) :
  Fin.to_nat i <> Fin.to_nat j -> Vector.nth t i = Vector.nth (Vector.replace t j x) i.
Proof.
  revert j. induction i; dependent destruct t; dependent destruct j; simpl; try tauto.
  apply IHi. contradict H. cbn. now rewrite !H.
Qed.
 *)

Instance Vector_eq_dec n A: eq_dec A -> eq_dec (Vector.t A n).
Proof.
  intros H x y. eapply VectorEq.eq_dec with (A_beq := fun x y => proj1_sig (Sumbool.bool_of_sumbool (H x y))).
  intros ? ?. destruct (Sumbool.bool_of_sumbool).
  cbn.  destruct x1;intuition.
Defined.

Instance Fin_eq_dec n : eq_dec (Fin.t n).
Proof.
  intros; hnf.
  destruct (Fin.eqb x y) eqn:E.
  - left. now eapply Fin.eqb_eq.
  - right. intros H. eapply Fin.eqb_eq in H. congruence.
Defined.


Import VectorNotations.
Lemma Vector_map_app {X Y k1 k2} (v1 : Vector.t X k1) (v2 : Vector.t X k2) (f : X -> Y) :
  Vector.map f (v1 ++ v2)%vector = Vector.map f v1 ++ Vector.map f v2.
Proof.
  induction v1; cbn; congruence.
Qed.

Lemma Vector_in_app {X n1 n2} (x : X) (v1 : Vector.t X n1) (v2 : Vector.t X n2):
  Vector.In x (v1 ++ v2) <-> Vector.In x v1 \/ Vector.In x v2.
Proof.
  induction v1; cbn.
  - firstorder. inversion H.
  - split.
    + intros [-> | H] % In_cons.
      * left. econstructor.
      * eapply IHv1 in H as [ | ]; eauto. left. now econstructor.
    + intros [ [ -> | ] % In_cons | ]; econstructor; intuition.
Qed.

Lemma vect_in_map (X Y : Type) (n : nat) (f : X -> Y) (V : Vector.t X n) (x : X) :
  In x V -> In (f x) (map f V).
Proof. induction 1; cbn; constructor; auto. Qed.

Lemma vect_in_map_iff (X Y : Type) (n : nat) (f : X -> Y) (V : Vector.t X n) (y : Y) :
  In y (map f V) <-> (exists x : X, f x = y /\ In x V).
Proof.
  split.
  - intros H. induction V; cbn in *.
    + inv H.
    + apply In_cons in H as [ <- | H].
      * exists h. split; auto. now constructor 1.
      * specialize (IHV H) as (x&Hx1&Hx2). exists x. split; auto. now constructor 2.
  - intros (x&<-&H). now apply vect_in_map.
Qed.


Lemma In_replace (X : Type) (n : nat) (xs : Vector.t X n) (i : Fin.t n) (x y : X) :
  In y (replace xs i x) -> (x = y \/ In y xs).
Proof.
  revert i x y. induction xs; intros; cbn in *.
  - inv i.
  - dependent destruct i; cbn in *; apply In_cons in H as [-> | H]; auto; try now (right; constructor).
    specialize (IHxs _ _ _ H) as [-> | IH]; [ now left | right; now constructor ].
Qed.

Lemma In_replace' (X : Type) (n : nat) (xs : Vector.t X n) (i : Fin.t n) (x y : X) :
  In y (replace xs i x) -> x = y \/ exists j, i <> j /\ xs[@j] = y.
Proof.
  revert i x y. induction xs; intros; cbn -[nth] in *.
  - inv i.
  - dependent destruct i; cbn -[nth] in *.
    + apply In_cons in H as [->|H].
      * tauto.
      * apply vect_nth_In' in H as (j&H). right. exists (Fin.FS j). split. discriminate. cbn. assumption.
    + apply In_cons in H as [->|H].
      * right. exists Fin.F1. split. discriminate. cbn. reflexivity.
      * specialize (IHxs _ _ _ H) as [-> | (j&IH1&IH2)]; [ tauto | ].
        right. exists (Fin.FS j). split. now intros -> % Fin.FS_inj. cbn. assumption.
Qed.




(* Tactic for simplifying a hypothesis of the form [In x v] *)


Ltac simpl_vector_inv :=
  repeat match goal with
         | [ H : [| |] = (_ ::: _) |- _ ] => solve [discriminate H]
         | [ H : (_ ::: _) = [| |]  |- _ ] => solve [discriminate H]
         | [ H : Fin.F1 = Fin.FS _ |- _] => solve [discriminate H]
         | [ H : Fin.FS _ = Fin.F1 |- _] => solve [discriminate H]
         | [ H : Fin.FS ?i = Fin.FS ?j |- _] =>
           simple apply Fin.FS_inj in H;
           first [is_var i;move H at bottom;subst i | is_var j;move H at bottom;subst j | idtac]
         end.


Ltac simpl_vector_in :=
  repeat
    match goal with
    | _ => first
            [ progress destruct_vector_in
            | progress simpl_vector_inv
            | progress auto
            | congruence
            ]
    | [ H : Vector.In _ (Vector.map _ _) |- _] =>
      let x := fresh "x" in
      eapply vect_in_map_iff in H as (x&<-&H)
    | [ H : Vector.In _ (Vector.map _ _) |- _] =>
      let x := fresh "x" in
      let H' := fresh H in
      eapply vect_in_map_iff in H as (x&H&H')
    | [ H : Vector.In _ (tabulate _) |- _ ] =>
      let i := fresh "i" in
      apply in_tabulate in H as (i&->)
    | [ H : Vector.In _ (tabulate _) |- _ ] =>
      let i := fresh "i" in
      let H := fresh "H" in
      apply in_tabulate in H as (i&H)
    end.

Ltac vector_not_in :=
  let H := fresh "H" in
  intros H; simpl_vector_in.

Goal Vector.In (Fin.F1 (n := 10)) [|Fin1; Fin2; Fin3 |] -> False.
Proof. intros H. simpl_vector_in. Qed.
  
Goal Vector.In (Fin.F1 (n := 10)) (map (Fin.FS) [|Fin0; Fin1; Fin2|]) -> False.
Proof. intros H. simpl_vector_in. Qed.



(* Conversion between vectors and lists *)
Module VecToListCoercion.
  Coercion Vector.to_list : Vector.t >-> list.
End VecToListCoercion.

Import VecToListCoercion.

Lemma tolist_In (X : Type) (n : nat) (xs : Vector.t X n) (x : X) :
  Vector.In x xs <-> List.In x xs.
Proof.
  split; intros H.
  - induction H; cbn; auto.
  - induction xs; cbn in *; auto. destruct H as [-> | H]; econstructor; eauto.
Qed.

Arguments Vector.eqb {_}  _ {_ _}.

Lemma vector_eqb_spec X n eqb:
  (forall (x1 x2 : X) , reflect (x1 = x2) (eqb x1 x2))
  -> forall x y , reflect (x=y) (Vector.eqb (n:=n) eqb x y).
Proof with try (constructor;congruence).
  intros Hf x y.
  apply iff_reflect. symmetry. apply Vector.eqb_eq. symmetry. apply reflect_iff. eauto.
Qed. 

Lemma vector_to_list_inj (X : Type) (n : nat) (xs ys : Vector.t X n) :
  Vector.to_list xs = Vector.to_list ys -> xs = ys.
Proof.
  revert ys. induction xs as [ | x n xs IH]; intros; cbn in *.
  - destruct_vector. reflexivity.
  - destruct_vector. cbn in *. inv H. f_equal. auto.
Qed.

Lemma vector_to_list_length (X : Type) (n : nat) (xs : Vector.t X n) :
  length(Vector.to_list xs) = n. 
Proof.
  induction xs as [ | x n xs IH]. 
  - now cbn. 
  - change (S (length xs) = S n). congruence.
Qed. 

Lemma vector_rev_append_tail_to_list A (n m: nat) (v : Vector.t A n) (w : Vector.t A m): 
Vector.to_list (Vector.rev_append_tail v w) = (List.rev (Vector.to_list v) ++ Vector.to_list w)%list.
Proof.
  unfold Vector.to_list. revert v m w. induction n;intros v;dependent destruct v;cbn. reflexivity.
  intros. specialize IHn with (w:=h:::w). cbn in *. rewrite IHn. autorewrite with list. easy.
Qed.

Lemma vector_rev_to_list A (n : nat) (v : Vector.t A n): 
  Vector.to_list (Vector.rev v) = List.rev (Vector.to_list v).
Proof.
  unfold Vector.rev,Vector.rev_append.
  specialize (vector_rev_append_tail_to_list v [| |]) as H'. cbn in H'.
  autorewrite with list in H'. rewrite <- H'. generalize (Vector.rev_append_tail v [| |]). 
  generalize (Plus.plus_tail_plus n 0). generalize (Plus.tail_plus n 0). generalize (plus_n_O n).
  intros -> ? <-. rewrite <- plus_n_O. reflexivity.
Qed.


Lemma vector_map_to_list A B (f : A -> B)(n : nat) (v : Vector.t A n): 
  Vector.to_list (Vector.map f v) = List.map f (Vector.to_list v).
Proof.
  unfold Vector.map, Vector.to_list. revert v;induction n;intros v;dependent destruct v;cbn. easy. now rewrite IHn.
Qed.


Lemma eq_nth_iff' X n (v w : Vector.t X n):
  (forall i : Fin.t n, v[@i] = w[@i]) -> v = w.
Proof. intros. eapply Vector.eq_nth_iff. now intros ? ? ->. Qed.



Lemma vector_fold_right_to_list (A B : Type) (f : A -> B -> B) (n : nat) (v : Vector.t A n) (a : B):
      Vector.fold_right f v a = List.fold_right f a (Vector.to_list v).
Proof.
  unfold Vector.to_list. induction n. all:destruct_vector. all:cbn;congruence.
Qed.
Lemma vector_fold_left_to_list (A B : Type) (f : A -> B -> A) (n : nat) (v : VectorDef.t B n) (a : A):
  VectorDef.fold_left f a v = List.fold_left f (Vector.to_list v) a.
Proof.
  unfold Vector.to_list. induction n in v,a|-*. all:destruct_vector. all:cbn;congruence.
Qed.

Lemma vector_fold_left_right (A B : Type) (f : A -> B -> A) (n : nat) (v : VectorDef.t B n) (a : A):
  Vector.fold_left f a v = Vector.fold_right (fun x y => f y x) (Vector.rev v) a.
Proof.
  rewrite vector_fold_right_to_list, vector_fold_left_to_list.
  setoid_rewrite <- List.rev_involutive at 2. rewrite List.fold_left_rev_right. f_equal.
  rewrite vector_rev_to_list,List.rev_involutive. easy.
Qed.

About eq_refl.
Require Import Equations.Type.DepElim.
About eq_refl.

Local Arguments Fin.of_nat_lt _ {_} _.

Lemma vector_nth_rev_append_tail_r' X n n' (v : Vector.t X n) (v' : Vector.t X n') i (i':=proj1_sig (Fin.to_nat i))
  j (H: i' = n + j) H':
  (Vector.rev_append_tail v v') [@ i] = v'[@ Fin.of_nat_lt j H'].
Proof.
  revert dependent n'. revert j.
  depind v;cbn;intros.
  {f_equal. subst j. erewrite Fin.of_nat_ext, Fin.of_nat_to_nat_inv. easy. }
  erewrite IHv with (v':=h::v') (j:=S j). 2:nia. cbn.
  f_equal. eapply Fin.of_nat_ext.
  Unshelve. nia.
Qed.

Lemma vector_nth_rev_append_tail_r X n n' (v : Vector.t X n) (v' : Vector.t X n') i (i':=proj1_sig (Fin.to_nat i))
  (H : n <= i') H':
  (Vector.rev_append_tail v v') [@ i] = v'[@ Fin.of_nat_lt (i' - n) H'].
Proof.
  revert dependent n'. 
  depind v;cbn;intros.
  {f_equal. revert H'. rewrite Nat.sub_0_r. intro. erewrite Fin.of_nat_ext, Fin.of_nat_to_nat_inv. easy. }
  unshelve erewrite IHv with (v':=h::v'). 3:nia. 1:abstract (clear - H'; nia).
  generalize (vector_nth_rev_append_tail_r_subproof n n' i H').
  destruct (proj1_sig (Fin.to_nat i) - n) eqn:H''. nia.
  cbn. intros. f_equal. revert H'. replace (proj1_sig (Fin.to_nat i) - S n) with n0 by nia. 
  intros. apply Fin.of_nat_ext.
Qed.

Lemma vector_nth_rev_append_tail_l X n n' (v : Vector.t X n) (v' : Vector.t X n') i (i':=proj1_sig (Fin.to_nat i))
  (H: i' < n) H':
  (Vector.rev_append_tail v v') [@ i] = v[@ Fin.of_nat_lt (n-1-i') H'].
Proof.
  revert dependent n'.
  depind v;cbn;intros. nia.
  revert H'. destruct (n - 0 - proj1_sig (Fin.to_nat i)) eqn:H';cbn.
  - unshelve erewrite vector_nth_rev_append_tail_r. 3:nia. 1:abstract nia.
    generalize (vector_nth_rev_append_tail_l_subproof n n' i H H').
    destruct (proj1_sig (Fin.to_nat i) - n) eqn:H''. 2:nia.
    reflexivity.
  - unshelve erewrite IHv. 3:nia. 1:abstract nia. intros. f_equal.
    generalize (vector_nth_rev_append_tail_l_subproof0 n n' i H n0 H').
    replace (n - 1 - proj1_sig (Fin.to_nat i)) with n0. 2:nia.
    intros. eapply Fin.of_nat_ext.
Qed.

Lemma vector_nth_rev X n (v : Vector.t X n) i H':
  (Vector.rev v) [@ i] = v[@ Fin.of_nat_lt (n -1-proj1_sig (Fin.to_nat i)) H'].
Proof.
  unfold Vector.rev, Vector.rev_append. 
  specialize (vector_nth_rev_append_tail_l v []). cbn zeta. 
  generalize (Vector.rev_append_tail v []). generalize (Plus.plus_tail_plus n 0).
  generalize (Plus.tail_plus n 0). generalize (plus_n_O n). generalize (n+0).
  intros ? -> ? <- ? H. apply H. now destruct Fin.to_nat.
Qed.


Lemma Vector_nth_L {X k1 k2} (v1 : Vector.t X k1) (v2 : Vector.t X k2) i :
  (v1 ++ v2)[@ Fin.L k2 i] = v1[@i].
Proof.
  revert k2 v2 i.
  dependent induction v1; intros.
  - dependent destruct i.
  - dependent destruct i.
    + reflexivity.
    + cbn. eapply IHv1.
Qed.

Lemma Vector_nth_R {X k1 k2} (v1 : Vector.t X k1) (v2 : Vector.t X k2) i :
  (v1 ++ v2)[@ Fin.R k1 i] = v2[@i].
Proof.
  revert k2 v2 i.
  dependent induction v1; intros.
  - reflexivity.
  - cbn. eapply IHv1.
  Qed.