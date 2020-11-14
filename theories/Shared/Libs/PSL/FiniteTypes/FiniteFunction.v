From Undecidability.Shared.Libs.PSL Require Import FinTypes Base.
From Undecidability.Shared.Libs.PSL Require Import Bijection.

(* Require Import Vector. *)

(* Definition vector X Y := Vector.t Y (|elem X|). *)

Definition finfunc_table (A : finType) (B: Type) (f: A -> B) :=
  List.map (fun x => (x, f x)) (elem A).

(* Now we prove that the tranformation of a function of finite domain to a table is correct *)

Lemma finfunc_comp (A : finType) (B: Type) (f: A -> B) a : (a,f a) el finfunc_table f.
Proof.
  unfold finfunc_table. now eapply (in_map (fun x => (x, f x))).
Qed.

Lemma finfunc_sound (A : finType) (B : Type) (f: A -> B) a b: (a,b) el finfunc_table f -> b = f a.
Proof.
  unfold finfunc_table. rewrite in_map_iff. firstorder congruence.
Qed.

Lemma finfunc_sound_cor (A : finType) (B:Type) (f: A -> B) a b b' : (a,b) el finfunc_table f -> (a,b') el finfunc_table f -> b = b'.
Proof.
  intros H1 H2. specialize (finfunc_sound H1). specialize (finfunc_sound H2). congruence. 
Qed.


Definition lookup (A : eqType) (B : Type) (l : list (A * B)) (a : A) (def : B) : B :=
  match (filter (fun p => Dec (fst p = a)) l) with
    List.nil => def
  | p :: _ => snd p
  end.


Lemma lookup_sound (A: eqType) (B: Type) (L : list (prod A B)) a b def :
  (forall a' b1 b2, (a',b1) el L -> (a',b2) el L -> b1=b2) -> (a,b) el L -> lookup L a def = b.
Proof.
  intros H1 H2. unfold lookup.
  destruct filter eqn:E.
  - assert ((a,b) el filter (fun p : A * B => Dec (fst p = a)) L) by ( rewrite in_filter_iff ; eauto).
    now rewrite E in H. 
  - destruct p. assert ((e,b0) el (filter (fun p : A * B => Dec (fst p = a)) L)) by now rewrite E.
    rewrite in_filter_iff in H. 
    dec; cbn in *; subst; firstorder.
Qed.

Lemma lookup_complete (A: eqType) (B: Type) (L : list (prod A B)) a def :
  {(a,lookup L a def) el L } + {~(exists b, (a,b) el L) /\ lookup L a def  = def}.
Proof.
  unfold lookup.
  destruct filter eqn:E.
  - right. split. 2:easy.
    intros (x&?).
    assert ((a,x) el filter (fun p : A * B => Dec (fst p = a)) L).
    {rewrite in_filter_iff;cbn. decide _;try easy. }
    rewrite E in H0. easy. 
  - assert (p el (filter (fun p : A * B => Dec (fst p = a)) L)) by now rewrite E.
    rewrite in_filter_iff in H.
    destruct p.
    dec; cbn in *; subst; firstorder.
Qed.

Lemma finfunc_correct (A: finType) B (f: A -> B) a  def: lookup (finfunc_table f) a def = f a.
Proof.
  eapply lookup_sound; [ apply finfunc_sound_cor | apply finfunc_comp ].
Qed.


(* Now we can prove that the transformation of the function table into another type is correct as long
as the conversion is injective *)

Lemma finfunc_conv (A: finType) (cA : eqType) (B cB : Type) (f: A -> B) (mA : A -> cA) (mB : B -> cB) a def:
  injective mA -> lookup (List.map (fun x => (mA (fst x), mB (snd x))) (finfunc_table f))  (mA a) def = mB (f a).
Proof.
  intros INJ.
  erewrite lookup_sound; eauto.
  - intros a' b1 b2 H1 H2. rewrite in_map_iff in *. destruct H1 as [[] [L1 R1]]. destruct H2 as [[] [L2 R2]].
    cbn in *.
    inv L1; inv L2. rewrite (finfunc_sound R1), (finfunc_sound R2), (INJ e e0); congruence.
  - rewrite in_map_iff. exists (a, f a). subst. split; auto. apply finfunc_comp.
Qed.




(* (** * Definition of vectors (extensional/ set theoretic functions)  *)
 (*   structure containing a list representing the image and a proof that the list has exactly as many elements as the source type *) *)
(* Definition Card_X_eq X Y (A: list Y) := |A| = Cardinality X. *)
(* Definition vector (X: finType) (Y: Type) := subtype (@Card_X_eq X Y). *)
(* Notation "X --> Y" := (vector X Y) (at level 55, right associativity). *)
(* Hint Unfold pure. *)
(* Hint Unfold Card_X_eq. *)
(* (** Projects the list from a STF *) *)
(* Definition image (X: finType) (Y: Type) (f: X --> Y) := proj1_sig  f. *)

(* (** Instance Declaration for Type Dec Type class for vectors. *) *)
(* Instance vector_eq_dec (X: finType) (Y: eqType) : eq_dec (X --> Y). *)
(* Proof. *)
(*   auto. *)
(* Qed. *)

(* Canonical Structure EqVect (X: finType) (Y: eqType) := EqType (X --> Y). *)

(* (** Function which produces a list of all list containing elements from A with length n *) *)
(* Fixpoint images (Y: Type) (A: list Y) (n: nat): list (list Y) := *)
(*   match n with *)
(*   | 0 => [[]] *)
(*   | S n' => concat (map (fun x => map (cons x) (images A n')) A) *)
(*   end. *)

(* Lemma imagesNonempty (Y: Type) y (A: list Y) : forall n, images (y::A) n <> nil. *)
(* Proof. *)
(*   intro n. induction n. *)
(*   - cbn. congruence. *)
(*   - cbn. intro H. pose proof (app_eq_nil _ _ H) as [E1 E2]. clear H. pose proof (map_eq_nil _ _ E1).  auto. *)
(* Qed. *)

(* (** If x is unequal to y then a list starting with y cannot be found in a list of list all starting with x *) *)
(* Lemma notInMapCons (X: Type) (x y: X) (A: list X) (B: list (list X)): *)
(*   x <> y -> y::A el (map (cons x) B) -> False. *)
(* Proof. *)
(*   intros neq E. rewrite in_map_iff in E. destruct E as [C [E _]]. congruence. *)
(* Qed. *)

(* Definition mC X B := (fun x:X => map (cons x) B). *)
(* Definition mmC  X B (A: list X) := map (mC B) A. *)

(* Lemma disjoint_map_cons X (A: list (list X)) (x y: X): x <> y -> disjoint (map (cons x) A) (map (cons y) A). *)
(* Proof. *)
(*   intro N; induction A. *)
(*   - cbn. auto. *)
(*   - cbn. unfold disjoint. intros [B [H1 H2]]. destruct H1, H2. *)
(*     + congruence. *)
(*     + subst B. eapply notInMapCons. Focus 2. *)
(*       * apply H0. *)
(*       * congruence. *)
(*     + subst B. eapply notInMapCons; eauto. *)
(*     + apply IHA. now exists B. *)
(* Qed.   *)

(* Lemma disjoint_in (X: Type) x A (B: list (list X)) (E: B <> nil) B' (H: ~ x el A): B' el map (mC B) A -> disjoint (map (cons x) B) B'.  *)
(* Proof. *)
(*   destruct B; try congruence. *)
(*   intro H'. induction A. *)
(*   - contradiction H'. *)
(*   - pose proof (negOr H) as [G G']. destruct H' as [H' | H']. *)
(*     + subst B'. apply disjoint_map_cons; congruence. *)
(*     + apply IHA; auto. *)
(* Qed. *)

(* Lemma disjoint_in_map_map_cons X  (A: list X) (B C C': list (list X)) (H: C <> C') (E: C el (mmC B A)) (E': C' el (mmC B A)) (N: B <> nil) (D: dupfree A): *)
(*   disjoint C C'. *)
(* Proof.  *)
(*   induction D. *)
(*   - contradiction E. *)
(*   - destruct B; try congruence; clear N. destruct E, E'; try congruence. *)
(*     + subst C. eapply disjoint_in; now eauto. *)
(*     + subst C'. apply disjoint_symm. eapply disjoint_in; now  eauto. *)
(*     + now apply IHD. *)
(* Qed.       *)

(* Lemma dupfree_concat_map_cons (X: Type) (A: list X) (B: list (list X)): *)
(*   dupfree A -> dupfree B -> B <> nil ->  dupfree (concat (map (fun x => map (cons x) B) A)). *)
(* Proof. *)
(*   intros D D' N. apply dupfree_concat; try split. *)
(*   - intros C E. induction D. *)
(*     +  contradiction E. *)
(*     + destruct E; auto. subst C. apply dupfree_map; auto. congruence. *)
(*   -  intros B' B'' E E' H. eapply disjoint_in_map_map_cons; eauto. *)
(*   - apply dupfree_map; auto. intros x y _ _ E. destruct B. *)
(*     + congruence. *)
(*     +  cbn in E. now inv E. *)
(* Qed. *)

(* Lemma imagesDupfree (Y: Type) (A: list Y) (n:nat) : dupfree A -> dupfree (images A n). *)
(* Proof. *)
(*   induction n. *)
(*   - now repeat constructor. *)
(*   - cbn. intro D. destruct A. *)
(*     +constructor. *)
(*     + apply dupfree_concat_map_cons; auto. apply imagesNonempty. *)
(* Qed. *)

(* Lemma inConcatCons (Y: Type) (A C: list Y) (B: list (list Y)) y: y el A /\ C el B -> (y::C) el (concat (map (fun x => map (cons x) B) A)). *)
(* Proof. *)
(*   intros [E E']. induction A. *)
(*   - contradiction E. *)
(*   - cbn. destruct E as [E | E]. *)
(*     + subst a. apply in_app_iff. left. apply in_map_iff. now exists C. *)
(*                                                                     + auto.  *)
(* Qed.                                                                *)

(* Lemma inImages (Y: Type) (A B: list Y): (forall x, x el B -> x el A) -> B el images A (|B|). *)
(* Proof. *)
(*   intros E. induction B. *)
(*   - cbn. now left. *)
(*   - cbn. apply inConcatCons. auto. *)
(* Qed.       *)

(* (** images produces a list of containing all lists of correct length *) *)
(* Lemma vector_enum_ok (X: finType) (Y: finType) f: *)
(* |f| = Cardinality X -> count (images  (elem Y) (Cardinality X)) f= 1. *)
(* Proof. *)
(*   intros H. apply dupfreeCount. *)
(*   - apply imagesDupfree. apply dupfree_elements. *)
(*   - rewrite <- H. now apply inImages. *)
(* Qed. *)

(* (** FunctionLists A n only produces lists of length n *) *)
(* Lemma imagesInnerLength (Y: Type) (n: nat) : *)
(*   forall (A: list Y) B, B el (images A n) -> | B | = n. *)
(* Proof. *)
(*   induction n; intros A B; cbn. *)
(*   - intros H. destruct H; try tauto. now subst B. *)
(*   - pattern A at 1. generalize A at 2. induction A; cbn. *)
(*     +  tauto. *)
(*     + intros C E. destruct (in_app_or  _ _ B E) as [H|H]. *)
(*       * pose proof (in_map_iff (cons a)  (images C n) B) as [G _]. specialize (G H); clear H. *)
(*         destruct G as [D [H G]]. specialize (IHn  _ _ G). subst B. cbn. lia. *)
(*       * now apply (IHA C). *)
(* Qed. *)

(* (** Function converting a list (list Y) containing lists of length Cardinality X into a lists of vectors (X --> Y) *) *)
(* Definition extensionalPower (X Y: finType) (L: list (list Y))  (P: L <<= images (elem Y) (Cardinality X)): list (X --> Y). *)
(* Proof. *)
(*   revert L P. *)
(*   refine (fix extPow L P :=  _). destruct L. *)
(*   -  exact nil. *)
(*   - apply cons. *)
(*     + exists l. specialize (P l (or_introl eq_refl)). unfold pure. dec; auto. contradiction ( n (imagesInnerLength P)). *)
(*     + eapply extPow. intros A E. apply P. exact (or_intror E). *)
(* Defined. *)

(* (** To vectors  are equal if there images are equal *) *)
(* Lemma vector_extensionality (X: finType) (Y: Type) (F G: X --> Y) : (image F = image G) -> F = G. *)
(* Proof. *)
(*   apply subtype_extensionality.  *)
(* Qed. *)

(* (** The number if occurences of a function in extensionalpower is equal to the number of occurences of its image in the original list given to extensionalpower as an argument *) *)
(*  Lemma counttFL X Y L P f : *)
(*   count (@extensionalPower X Y L P) f = count L (image f). *)
(* Proof. *)
(*   induction L. *)
(*   -   reflexivity. *)
(*   - simpl. dec; rename a into A; decide (image f = A). *)
(*     +  now rewrite IHL. *)
(*     +contradict n. now subst f.       *)
(*     +  contradict n. now apply vector_extensionality. *)
(*     + apply IHL.         *)
(* Qed. *)

(* Instance finTypeC_vector (X Y: finType) : *)
(*   finTypeC (EqVect X Y). *)
(* Proof. *)
(*  apply (FinTypeC (enum := @extensionalPower _ _ (images (elem Y) (Cardinality X)) (fun x => fun y => y))). *)
(*  intro f. rewrite counttFL. apply vector_enum_ok. destruct f as [A p]. cbn. now impurify p. *)
(* Defined. *)

(* Canonical Structure finType_vector (X Y: finType) := FinType (EqVect X Y). *)

(* Notation "Y ^ X" := (finType_vector X Y). *)

(* Lemma finType_vector_correct (X Y: finType): *)
(*   X --> Y =  Y^ X. *)
(* Proof. *)
(*   reflexivity. *)
(* Qed. *)

(* Lemma finType_vector_enum (X Y: finType): *)
(*   elem (Y^ X) = @extensionalPower _ _ (images (elem Y) (Cardinality X)) (fun x => fun y => y). *)
(* Proof. *)
(*   reflexivity. *)
(* Qed. *)

(* Set Printing Coercions. *)

(* Lemma tofinType_vector_correct (X Y: finType): *)
(*   tofinType (X --> Y) = Y ^ X. *)
(* Proof. *)
(*   reflexivity. *)
(* Qed. *)
(* Unset Printing Coercions. *)
(* (** ** Conversion between vectors and functions *) *)


(* (** Function that applies a vector to an argument *)                 *)
(* Definition applyVect (X: finType) (Y: Type) (f: X --> Y): X -> Y. *)
(* Proof. *)
(*   refine (fun x: X => _). *)
(*   destruct (elem X) eqn: E. *)
(*   - exfalso. pose proof (elem_spec x). now rewrite E in H.     *)
(*   - destruct f as [image p]. destruct image. *)
(*     + exfalso. unfold Card_X_eq, Cardinality in p. rewrite E in p. now impurify p. *)
(*     + exact (getAt (y::image0) (index x) y). *)
(* Defined. *)

(* Coercion applyVect: vector >-> Funclass. *)

(* (** A function converting A function f into the list representing its image on elements of A*) *)
(* Definition getImage {X: finType} {Y: Type} (f: X -> Y) :=map f (elem X). *)

(* (** getImage contains the right elements *) *)
(* Lemma getImage_in (X: finType) (Y: Type) (f: X -> Y) (x:X) : (f x) el (getImage f). *)
(* Proof. *)
(*   unfold getImage. now apply in_map. *)
(*  Qed. *)
(* (** getImage only produces lists of the correct length *) *)
(* Lemma getImage_length (X: finType) (Y: Type) (f: X -> Y) :  |getImage f| = Cardinality X. *)
(* Proof. *)
(*   apply map_length. *)
(* Qed. *)

(* (** Function converting a function into a vector *) *)
(* Definition vectorise {X: finType} {Y: Type} (f: X -> Y) : X --> Y := *)
(*   exist (pure (@Card_X_eq X Y)) (getImage f) (purify (getImage_length f)). *)

(* Lemma getImage_correct (X:finType) (Y:Type) (f: X -> Y): *)
(*   getImage f = image (vectorise f). *)
(* Proof. *)
(*   reflexivity. *)
(* Qed. *)

(* (** A generalisation of a late case of apply_toVector_inverse *) *)
(* Lemma HelpApply (X: eqType) (Y: Type) (A: list X) (f: X -> Y) x y (C: count A x > 0): *)
(*   getAt (map f A) (getPosition A x) y = f x. *)
(* Proof. *)
(*   induction A. *)
(*   - cbn in *. lia. *)
(*   - cbn in *. dec. *)
(*     + congruence. *)
(*     + now apply IHA. *)
(* Qed. *)

(* (** If a function is converted into a vector and then applied to an argument the result is the same as if one had just applied the function to the argument *) *)
(* Lemma apply_vectorise_inverse (X: finType) (Y: Type) (f: X -> Y) (x: X) : *)
(*     (vectorise f) x = f x.   *)
(* Proof. *)
(*  destruct X as [X [A ok]]. destruct A. *)
(*   - discriminate (ok x). *)
(*   - cbn  in  *. specialize (ok x). dec. *)
(*     + congruence. *)
(*     + apply HelpApply. lia. *)
(* Qed. *)

(* (** The position of x in a list containg x exactly once is one greater than the size of the sublist befor x *) *)
(* Lemma countNumberApp (X: eqType) (x:X) (A B: list X)  (ok : count (A ++ x::B) x = 1) : *)
(*   getPosition (A ++ x::B) x = |A|. *)
(* Proof. *)
(*   induction A. *)
(*   - cbn. now deq x. *)
(*   - cbn in *. dec. *)
(*     + inv ok. pose proof (countApp a A B). lia. *)
(*     + auto. *)
(* Qed. *)

(* Lemma getAt_correct (Y:Type) (A A': list Y) y y': *)
(* getAt (A' ++ y::A) (|A'|) y' = y. *)
(* Proof. *)
(*   induction A'; cbn. *)
(*   - reflexivity. *)
(*   - cbn in *. apply IHA'. *)
(* Qed.     *)

(* Lemma rightResult (X: finType) (x:X) (B B': list X) (Y: Type)  (y:Y) (A A': list Y) (H:  pure (@Card_X_eq X Y) (A' ++ y::A))  (H': |A'| = | B'|)  (G: elem X = B' ++ x::B): *)
(*  ((exist _ _ H): X --> Y) x = y. *)
(* Proof. *)
(* destruct X as [X [C ok]]. unfold applyVect. cbn in *. subst C. destruct B'; destruct A' ; cbn in *; impurify H; unfold Card_X_eq in H;  cbn in H. *)
(*   -  now deq x.  *)
(*   -  rewrite app_length in H.  inv H. lia. *)
(*   - rewrite app_length in H. cbn in H. lia. *)
(*   - specialize (ok x). dec. *)
(*     + subst e. inv ok.  pose proof countApp x B' B. lia. *)
(*     + rewrite countNumberApp; auto. *)
(*    inv H'. eapply getAt_correct. *)
(* Qed.       *)

(* Lemma vectorise_apply_inverse' (X: finType) (B B': list X) (Y: Type) (A A' A'': list Y) (H: pure (@Card_X_eq X Y) A'') (H': |A'| = | B' |) (H'': |A| = | B|) (E: A' ++ A = A'') (G: elem X = B' ++ B) : *)
(*   map ((exist _ _ H): X --> Y) B= A. *)
(*   Proof. *)
(*     revert A A' B' H' H'' E G. induction B; intros A A' B' H' H'' E G. *)
(*     - cbn. symmetry. now rewrite <- length_zero_iff_nil. *)
(*     - cbn. destruct A; try (discriminate H''). f_equal. *)
(*       +  subst A''. eapply rightResult. *)
(*         * inv H'. exact H1. *)
(*         * exact G. *)
(*       + apply (IHB A (A' ++ [y]) (B' ++ [a])). *)
(*         * repeat rewrite app_length. cbn. lia. *)
(*         * now inv H''. *)
(*         *  now rewrite app_assoc_reverse. *)
(*         * rewrite G.  replace (a::B) with ([a]++B) by auto. now rewrite app_assoc. *)
(*   Qed. *)

(* Lemma vectorise_apply_inverse (X: finType) (Y: Type) (f: X --> Y): vectorise f = f. *)
(* Proof. *)
(*   apply vector_extensionality. cbn. destruct f as [A p]. *)
(*   eapply vectorise_apply_inverse'; eauto using app_nil_l; now impurify p. *)
(* Qed. *)

