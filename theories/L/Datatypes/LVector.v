From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L.Datatypes Require Import LNat Lists LFinType.

Require Import PslBase.Vectors.Vectors.

(** *** Encoding vectors *)

Instance register_vector X `{registered X} n : registered (Vector.t X n).
Proof.
  apply (registerAs VectorDef.to_list).
  intros x. induction x.
  - intros y. pattern y. revert y. eapply VectorDef.case0. cbn. reflexivity.
  - intros y. clear H. revert h x IHx. pattern n, y. revert n y.
    eapply Vector.caseS. intros h n y h0 x IHx [=].
    subst. f_equal. eapply IHx. eassumption.
Defined.

Instance term_to_list X `{registered X} n : computableTime' (Vector.to_list (A:=X) (n:=n)) (fun _ _ => (1,tt)).
Proof.
  apply cast_computableTime.
Qed.

Instance term_vector_map X Y `{registered X} `{registered Y} n (f:X->Y) fT:
  computableTime' f fT ->
  computableTime' (VectorDef.map f (n:=n))
                 (fun l _ => (map_time (fun x=> fst (fT x tt)) l + 3,tt)).
Proof.
  intros ?.
  computable_casted_result.
  apply computableTimeExt with (x:= fun x => map f (Vector.to_list x)).
  2:{
    extract.
    solverec.
  }

  cbn. intros x.
  clear - x.
  induction n. revert x. apply VectorDef.case0. easy. revert IHn. apply Vector.caseS' with (v:=x).
  intros. cbn. f_equal. fold (Vector.fold_right (A:=X) (B:=Y)).
  setoid_rewrite IHn. reflexivity.
Qed.

(* Instance term_vector_map X Y `{registered X} `{registered Y} n (f:X->Y): computable f -> computable (VectorDef.map f (n:=n)). *)
(* Proof. *)
(*   intros ?. *)

(*   internalize_casted_result. *)
(*   apply computableExt with (x:= fun x => map f (Vector.to_list x)). *)
(*   2:{ *)
(*     extract. *)
(*   } *)

(*   cbn. intros x.  *)
(*   clear - x. *)
(*   induction n. revert x. apply VectorDef.case0. easy. revert IHn. apply Vector.caseS' with (v:=x). *)
(*   intros. cbn. f_equal. fold (Vector.fold_right (A:=X) (B:=Y)). *)
(*   setoid_rewrite IHn. reflexivity. *)
(* Qed. *)

Fixpoint time_map2 {X Y Z} `{registered X} `{registered Y} `{registered Z} (gT : timeComplexity (X->Y->Z)) (l1 :list X) (l2 : list Y) :=
  match l1,l2 with
  | x::l1,y::l2 => callTime2 gT x y + 18 + time_map2 gT l1 l2
  | _,_ => 9
  end.
Instance term_map2 n A B C `{registered A} `{registered B} `{registered C} (g:A -> B -> C) gT:
  computableTime' g gT-> computableTime' (Vector.map2 g (n:=n)) (fun l1 _ => (1,fun l2 _ => (time_map2 gT (Vector.to_list l1) (Vector.to_list l2) +8,tt))).
Proof.
  intros ?.
  computable_casted_result.
  pose (f:=(fix f t a : list C:=
              match t,a with
                t1::t,a1::a => g t1 a1 :: f t a
              | _,_ => []
              end)).
  assert (computableTime' f (fun l1 _ => (5,fun l2 _ => (time_map2 gT l1 l2,tt)))).
  {subst f; extract.



   solverec. }
  apply computableTimeExt with (x:= fun t a => f (Vector.to_list t) (Vector.to_list a)).
  2:{extract. solverec. }
  induction n;cbn.
  -do 2 destruct x using Vector.case0. reflexivity.
  -destruct x using Vector.caseS'. destruct x0 using Vector.caseS'.
   cbn. f_equal. apply IHn.
Qed.


Lemma time_map2_leq X Y Z `{registered X}  `{registered Y}  `{registered Z}  (fT:timeComplexity (X -> Y -> Z))(l1 : list X) (l2:list Y) k:
  (forall x y, callTime2 fT x y <= k) ->
  time_map2 fT l1 l2<= length l1 * (k+18) + 9.
Proof.
  intros H';
    induction l1 in l2|-*;cbn [time_map2].
  -intuition.
  -destruct l2;ring_simplify. intuition.
   rewrite H',IHl1. cbn [length]. ring_simplify. intuition.
Qed.

Instance term_vector_eqb X `{registered X} (n' m:nat) (eqb:X->X->bool) eqbT:
  computableTime' eqb eqbT
  -> computableTime'
      (VectorEq.eqb eqb (A:=X) (n:=n') (m:=m))
      (fun A _ => (1,fun B _ => (list_eqbTime eqbT (Vector.to_list A) (Vector.to_list B) + 9,tt))).
Proof.
  intros ?.
  apply computableTimeExt with (x:=(fun x y => list_eqb eqb (Vector.to_list x) (Vector.to_list y))).
  2:{extract.
     solverec. }
  intros v v'. hnf.
  induction v in n',v'|-*;cbn;destruct v';cbn;try tauto. rewrite <- IHv. f_equal.
Qed.


Lemma to_list_length X n0 (l:Vector.t X n0) :length l = n0.
Proof.
  induction l. reflexivity. rewrite <- IHl at 3. reflexivity.
Qed.
