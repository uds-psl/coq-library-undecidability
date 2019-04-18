From smpl Require Import Smpl.
Require Import Omega.
Require Export Psatz Arith.
Require Export RelationClasses Morphisms.

(* Congruence Lemmatas over nat*)
Instance add_le_mono : Proper (le ==> le ==> le) plus.
Proof. repeat intro. now apply Nat.add_le_mono. Qed.

Instance mult_le_mono : Proper (le ==> le ==> le) mult.
Proof. repeat intro. now apply Nat.mul_le_mono. Qed.

Instance max_le_mono : Proper (le ==> le ==> le) max.
Proof. repeat intro. repeat eapply Nat.max_case_strong;omega. Qed.

Instance max'_le_mono : Proper (le ==> le ==> le) Init.Nat.max.
Proof. repeat intro. repeat eapply Nat.max_case_strong;omega. Qed.

Instance S_le_mono : Proper (le ==> le) S.
Proof. repeat intro. omega. Qed.

(* (* Congruence Lemmatas over Z*) *)
(* Instance add_leZ_mono : Proper (Z.le ==> Z.le ==> Z.le) Z.add. *)
(* repeat intro. eapply Z.add_le_mono. 3:eassumption. all:eauto.  *)
(* Qed. *)

(* Instance max_leZ_mono : Proper (Z.le ==> Z.le ==> Z.le) Z.max. *)
(* intros ? ? ? ? ? ?. repeat apply Z.max_case_strong;omega. *)
(* Qed. *)

(*Instance mult_leZ_mono : Proper (Z.le ==> Z.le ==> Z.le) Z.mul.
  intros ? ? ? ? ? ?. eapply Z.mul_le_mono;eassumption.
  Qed.*)


(* Transformation of nat to Z*)
(*
Lemma Z2Nat_id_max n:Z.of_nat (Z.to_nat n) = Z.max 0 n.
Proof.
  apply Z.max_case_strong. 2:intros;now apply Z2Nat.id.
  intros H. rewrite <- Nat2Z.inj_0. apply inj_eq. destruct n;cbn. 1,3:tauto. cbv in H. tauto.
Qed.

Ltac Nat2Z' :=
  lazymatch goal with
  | |- Z.of_nat (_ + _)%nat = _ => etransitivity;[apply Nat2Z.inj_add|apply f_equal2;Nat2Z'..]
  | |- Z.of_nat (_ * _)%nat = _  => etransitivity;[apply Nat2Z.inj_mul|apply f_equal2;Nat2Z'..]
  | |- Z.of_nat (_ - _)%nat = _  => etransitivity;[apply Nat2Z.inj_sub_max|apply f_equal2;[ |apply f_equal2];Nat2Z'..]
  | |- Z.of_nat (Init.Nat.max _ _)%nat = _  => etransitivity;[apply Nat2Z.inj_max|apply f_equal2;Nat2Z'..]

  | |- Z.of_nat (Z.to_nat _) = _  => etransitivity;[apply Z2Nat_id_max|Nat2Z'..]

                                                     
  | |- Z.of_nat (S ?c) = _ =>
    lazymatch isnatcst (S c) with
      true => let c' := eval cbv in (Z.of_nat (S c))
               in replace (Z.of_nat (S c)) with c';reflexivity 
    | _ => refine (_ : Z.of_nat(1 + c) = _);Nat2Z'
    end
      
  | |- Z.of_nat 0 = _ => cbv;reflexivity
  | |- _ => reflexivity
  end.

Ltac Nat2Z :=
  match goal with
    |- ?P ?x ?y =>
    let x' := fresh "x'" in
    let y' := fresh "y'" in                       
    evar (x':Z);evar (y':Z);
    let Hx := fresh "Hx" in
    assert (Hx:x'=x) by (subst x';symmetry;Nat2Z');
    let Hy := fresh "Hy" in        
    assert (Hy:y'=y) by (subst y';symmetry;Nat2Z');
    refine (eq_rect _ (fun y => P x y) (eq_rect _ (fun x => P x y') _ _ Hx) _ Hy)
    ;subst x';subst y';clear Hx Hy
  end.





(* Lemmas and Automation of simplifying dominating-lemmatas*)
Lemma dominated_lift2 (A B : filterType) (f g: B -> Z) :
  dominated B f g
  -> dominated (product_filterType A B) (fun '(_,y) => f y) (fun '(_,y) => g y).
Proof.
  intros [c H]. exists c. rewrite productP. eexists (fun _ => True),_.
  do 2 try split. apply filter_universe. eassumption.
  cbn. tauto.
Qed.
Lemma dominated_lift1 (A B : filterType) (f g: A -> Z) :
  dominated A f g
  -> dominated (product_filterType A B) (fun '(x,_) => f x) (fun '(x,_) => g x).
Proof.
  intros [c H]. exists c. rewrite productP. eexists _,(fun _ => True).
  do 2 try split. eassumption. apply filter_universe.
  cbn. tauto.
Qed.

Smpl Create bigO.
Ltac bigO_simpl := repeat (smpl bigO).
 

Smpl Add apply_nary dominated_sum_distr_nary : bigO.
Smpl Add apply_nary dominated_mul_cst_l_1_nary: bigO.
Smpl Add apply_nary dominated_max_distr_nary: bigO.
Hint Extern 
     1 => apply ultimately_lift1 : ultimately_greater.
Hint Extern 
     1 => apply ultimately_lift2 : ultimately_greater.

Smpl Add apply dominated_lift1 : bigO.
Smpl Add apply dominated_lift2 : bigO.

(* Smpl Add lazymatch goal with *)
(*            |- limit _ _ _ => now limit_trysolve *)
(*          end: bigO. *)

Smpl Add intros;omega : bigO.

Canonical Structure positive_filterType.
Canonical Structure product_filterType.

(*
Lemma dominated_cst_positive (c:Z) g:
  (forall x:Z, 0 <= x -> 1<= g x)%Z -> dominated _ (fun _ => c) g.
Proof.
  intros H. exists (Z.abs c). intros a H0. cbn in a. specialize (H _ H0). setoid_rewrite Z.abs_eq at 3. 2:omega. rewrite <- H. omega. apply Z.abs_nonneg.
Qed.

Lemma dominated_cst_positive_nary (c:Z) g:
  (forall x:Z, 0 <= x -> 1<= g x)%Z -> dominated _ (fun _ => c) g.
Proof.
  intros H. exists (Z.abs c). intros a H0. cbn in a. specialize (H _ H0). setoid_rewrite Z.abs_eq at 3. 2:omega. rewrite <- H. omega. apply Z.abs_nonneg.
Qed.
Smpl Add apply_nary dominated_cst_positive_nary : bigO. *)
Smpl Add apply_nary dominated_mul_cst_l_2_nary : bigO.
Smpl Add apply_nary dominated_mul_cst_l_1_nary : bigO.

Lemma dominated_var_positive g:
  (forall x, (0 <= x -> x <= g x)%Z) -> dominated _ (fun x => x) g.
Proof.
  intros H. exists 1%Z. rewrite positiveP. intros a H0. specialize H with (1:=H0). rewrite !Z.abs_eq. all:omega.
Qed.
Smpl Add apply dominated_var_positive : bigO.



Definition sizeZ {sig X} (cX:codable sig X) x:= Z.of_nat (size cX x).

(*     Ltac specialize_fin' H k :=
      lazymatch type of H with
      | forall i : Fin.t k , _ => idtac
      | forall i : Fin.t ?k' , _ =>
        let H' := fresh H in
        let i' := (eval cbn in (Fin.R k (Fin0) : Fin.t k'))
        in
        assert (H':=H i') ;
        let k':= constr:(S k) in 
        specialize_fin' H k'
      end.
    Ltac specialize_fin :=
         match goal with
           H : forall i : Fin.t _,_ |- _ => specialize_fin' H 0;clear H
         end.
        specialize_fin. *)

Module Big'. 
  Import BigEnough.Big.

  
  Ltac big_base_evar :=
    solve [repeat lazymatch goal with
             |- leq _ (?max _ _) => apply next
           | |- leq _ _ => apply here
           end].

  Module Exports.
    
    Ltac big_evar :=
      repeat (apply context; [ big_base_evar | .. ]);
      try tauto.
  End Exports.
End Big'.

Export Big'.Exports.
  
Module tmp.
  Local Unset Implicit Arguments. 
  Structure terminatesO {sig n} {A:filterType}  (M : mTM sig n ) (T : (A -> Z) -> tRel sig n) {le : A -> A -> Prop} (bound : A -> Z) :=
  {
    stepFun : A -> Z;
    stepFun_spec : M ↓ T stepFun;
    stepFun_dominated : dominated A stepFun bound;
    stepFun_nonneg : forall x, (0 <= stepFun x)%Z;
    stepFun_monotonic : monotonic le Z.le stepFun
  }.
End tmp.
Export tmp.
Existing Class terminatesO.
Arguments terminatesO _ _ _ _ _ _ _%Z_scope.
Arguments stepFun {_ _ _} _ {_ _ _ _} .

Hint Resolve stepFun_spec : TM_Correct.
Structure C : Type :=
  {
    carrier : Type;
    le_rel :> carrier -> carrier -> Prop
  }.

Ltac exact_le := match goal with |- _ * _ -> _ * _ -> Prop => apply LibRelation.lexico2;exact_le end.

Notation "M '↓@' T '∈O' bound" := (terminatesO (le:=@le_rel _) M T bound) (at level 60).

Canonical Structure C_Z := {|le_rel := (fun x y => (0 <= x <= y)%Z)|}.
Canonical Structure C_pair (A : C) (B: C):= {|le_rel := LibRelation.prod2 (@le_rel A) (@le_rel B)|}.

Lemma monotonic_prod2 A B C (f : A*B -> C) leA leB leC:
  Transitive leC
  -> (forall b, monotonic leA leC (fun a => f (a,b)))
  -> (forall a, monotonic leB leC (fun b => f (a,b)))
  -> monotonic (LibRelation.prod2 leA leB) leC f.
Proof.
  unfold monotonic, LibRelation.prod2. intros ? ? ? [] [] []. etransitivity;eauto.
Qed.

Lemma monotonic_prod_positive A C (f : A*Z -> C) leA leC:
  Transitive leC
  -> (forall b, (0 <= b)%Z -> monotonic leA leC (fun a => f (a,b)))
  -> (forall a, monotonic C_Z leC (fun b => f (a,b)))
  -> monotonic (LibRelation.prod2 leA C_Z) leC f.
Proof.
  unfold monotonic, LibRelation.prod2,C_Z;cbn. intros ? ? ? [] [] [? []]. etransitivity;eauto. apply H0;try omega. auto.
Qed.


Lemma dominated_cst_positive A c g:
  ultimately A (fun x => 1<= g x)%Z
  -> dominated A (fun _ => c) g.
Proof.
  intros H. exists (Z.abs c). unfold ultimately. destruct A as [A []].
  cbn in *. eapply u0. 2:exact H. exact u. cbn.  intros. setoid_rewrite Z.abs_eq at 3. 2:omega. rewrite <- H1. omega. apply Z.abs_nonneg.
Qed.

Lemma dominated_cst_positive_nary (domain : list Type) (M : Filter.mixin_of (Rtuple domain)) c (g: Rarrow domain Z_filterType):
  ultimately (nFilterType domain M) (fun x => 1<= App g x)%Z
  -> dominated (nFilterType domain M) (Const' domain c) (Uncurry g).
Proof.
  prove_nary dominated_cst_positive.
Qed.

Lemma ultimately_positive (P : _ -> Prop):
  (forall x, (0<=x)%Z -> P x)
  -> ultimately positive_filterType P.
Proof.
  intros. eassumption.
Qed.

Lemma ultimately_product_positive A (P : _ -> Prop):
  ultimately A (fun a => forall x, (0<=x)%Z -> P (a,x)) 
  -> ultimately (product_filterType A positive_filterType) P.
Proof.
  intros. rewrite productP.
  exists (fun a => forall x, (0<=x)%Z -> P (a, x)),(fun x => (0<=x)%Z). repeat split. eassumption. now intros ?. 
  intros. eauto.
Qed.


Lemma dominated_le_positive A f g:
  ultimately A (fun x => 0 <= f x <= g x)%Z
  -> dominated A f g.
Proof.
  intros H. exists 1%Z. unfold ultimately. destruct A as [A []].
  eapply u0. 2:exact H. exact u. intros. cbn in *|-. setoid_rewrite Z.abs_eq at 1 2.  all:omega.
Qed.

Lemma dominated_le_positive_nary (domain : list Type) (M : Filter.mixin_of (Rtuple domain)) (f g: Rarrow domain Z_filterType):
  ultimately (nFilterType domain M) (fun x => 0 <= App f x<= App g x)%Z
  -> dominated (nFilterType domain M) (Uncurry f) (Uncurry g).
Proof.
  prove_nary dominated_le_positive.
Qed.

Ltac prove_ultimately_nonnegatives := (repeat (apply ultimately_product_positive; cbn[fst snd]);apply ultimately_positive;intros;nia).

Smpl Add apply_nary dominated_cst_positive_nary;now prove_ultimately_nonnegatives : bigO.

Smpl Add 200 apply_nary dominated_le_positive_nary;now prove_ultimately_nonnegatives : bigO.


Ltac is_var_in_match t :=
  lazymatch t with
  | (fun p => match p with (x,y) => @?t' x y end) =>
    lazymatch t' with
      (fun x _ => @?t' x ) => is_var_in_match t'
    | (fun x _ => x )=> idtac
    | (fun _ x => x) => idtac
    end
  | (fun p => p) => idtac 
  end.



(* Smpl Add lazymatch goal with *)
(*            |- dominated _ ?f _ => is_var_in_match f; apply_nary dominated_le_positive_nary *)
                                                              
(*          end : bigO. *)

Ltac destruct_pair x :=
  is_var x;
  let t := type of x in
  lazymatch eval hnf in t with
    
    (_ * _)%type => let x' := fresh x in destruct x as [x x'];destruct_pair x
  | _ => idtac 
  end.

Ltac fun_pair n :=
  lazymatch eval hnf in n with
    1 => uconstr:(fun x => _)
  | S ?n =>
    let t := fun_pair n in
    uconstr:(fun '(x,y) => t x)      
  end.


Ltac bound_stepFun_dominated :=
  match goal with
    |- dominated ?F ?f ?g =>
    let L := domain_of_filter F in
    let n := (eval cbv in (length L)) in
    
    etransitivity;
    [
      let t1:= fun_pair n in
      let t2:= fun_pair n in
      (((refine (@dominated_comp_eq _ _ _ _ _ t2 _ t1 _ _ _); [notypeclasses refine (stepFun_dominated _ _ _ _) | | intros i;destruct_pair i.. ])); [ | | reflexivity| cbn beta;reflexivity])
    | cbn beta]
  end.
Smpl Add bound_stepFun_dominated;idtac "Workaround: looped 'smpl bigO' ('repeat smpl bigO' does not continue after bound_stepFun_ominated)"; bigO_simpl : bigO.

Lemma limit_product_nary domain M (B C : filterType) (f : Rarrow domain B) (g : Rarrow domain C):
  limit (nFilterType domain M) B (Uncurry f) ->
  limit (nFilterType domain M) C (Uncurry g) ->
  limit (nFilterType domain M) (product_filterType B C) (Fun' (fun i => (App f i, App g i))).
Proof.
  prove_nary limit_product.
Qed.

Smpl Add 101 apply_nary limit_product_nary : bigO.


Smpl Create monotonic.
Smpl Add 101
     (hnf;let H := fresh "H" in
          intros ? ? H;cbn in H;lazymatch goal with
                   |- (@stepFun _ _ _ _ _ _ _ ?t0 _ <= _)%Z =>
                   let H := fresh "H" in
                   assert (H:=@stepFun_monotonic _ _ _ _ _ _ _ t0);hnf in H;
                     rewrite H;[reflexivity| cbn;omega ]
                 end) : monotonic.
Smpl Add (apply monotonic_prod_positive;[exact _| let x := fresh "x" in intros x;destruct_pair x..]);[intro | ] : monotonic. 
Smpl Add simple apply monotonic_cst;apply preorder_of_PreOrder;exact _ : monotonic.
Smpl Add simple apply monotonic_sum : monotonic.
Smpl Add simple apply monotonic_max : monotonic.
Smpl Add simple apply monotonic_mul_cst_r;[omega| ] : monotonic.
Smpl Add simple apply monotonic_mul_cst_l;[omega| ] : monotonic.
Smpl Add simple apply monotonic_id : monotonic.
(* this is a hack. use nia instead. *)
Lemma  monotonic_id' :
  monotonic C_Z Z.le (fun x : positive_filterType => x).
Proof.
  hnf;cbn. tauto.
Qed.
Smpl Add simple apply monotonic_id' : monotonic.


Ltac monotonic := repeat smpl monotonic.


Lemma limitPos (A: filterType) (f : A -> Z) :
  limit A positive_filterType f <->
  ultimately A (fun x => 0 <= f x)%Z.
Proof.
  rewrite limitP.
  split.
  - intros H. apply H. rewrite positiveP. tauto.
  - intros H. intros P HP. rewrite positiveP in HP.
    eapply filter_closed_under_intersection. now apply filter_universe. eassumption.  auto.
Qed.

Smpl Add lazymatch goal with
           |- limit _ _ _ => apply limitPos; now prove_ultimately_nonnegatives
         end: bigO.
*)
