(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Nat Lia Relations.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_list finite php.

From Undecidability.TRAKHTENBROT
  Require Import notations.

Set Implicit Arguments.

Section gfp.

  (** We develop the theory of Kleene's greatest fixpoint for binary relations
      and establish the fact that the gfp is an equivalence (under suitable hyps),
      reached after omega many steps (under omega continuity) and
      reached after finitely many steps (under finiteness of the domain and
      preservation of decidability *)

  Variable (M : Type). 

  Implicit Type (R T : M -> M -> Prop).

  Notation "R ⊆ T" := (forall x y, R x y -> T x y).

  Notation "R 'o' T" := (fun x z => exists y, R x y /\ T y z) (at level 58).

  Let incl_trans R S T : R ⊆ S -> S ⊆ T -> R ⊆ T.
  Proof. firstorder. Qed.

  Let comp_mono R R' T T' : R ⊆ R' -> T ⊆ T' -> R o T ⊆ R' o T'.
  Proof. firstorder. Qed. 

  Variable (F : (M -> M -> Prop) -> M -> M -> Prop).

  Hypothesis (HF0 : forall R T, R ⊆ T -> F R ⊆ F T).  (* Monotonicity *)

  Let sym R := fun x y => R y x.

  Let i := iter F (fun _ _ => True).

  Let iS n : i (S n) = F (i n).
  Proof. apply iter_S. Qed.

  Let i0 : i 0 = fun _ _ => True.
  Proof. auto. Qed.

  Let i_S n : i (S n) ⊆ i n.
  Proof.
    unfold i.
    induction n as [ | n IHn ].
    + simpl; auto.
    + intros ? ?.
      rewrite iter_S with (n := n), iter_S.
      apply HF0, IHn.
  Qed.

  Let i_decr n m : n <= m -> i m ⊆ i n.
  Proof. induction 1; auto. Qed.

  Definition gfp x y := forall n, i n x y.

  Notation I := (@eq M).

  Hypothesis HF1 : I ⊆ F I.    (* Reflexivity *)

  Let i_refl n : I ⊆ i n.
  Proof.
    induction n as [ | n IHn ].
    + rewrite i0; auto.
    + rewrite iS.
      apply incl_trans with (1 := HF1), HF0, IHn.
  Qed.
  
  Let gfp_refl : I ⊆ gfp.
  Proof. intros ? ? [] ?; apply i_refl; auto. Qed.

  Hypothesis HF2 : forall R, sym (F R) ⊆ F (sym R).   (* Symmetry *)

  Let i_sym n : sym (i n) ⊆ i n.
  Proof.
    induction n as [ | n IHn ].
    + intros ? ?; rewrite i0; simpl; auto.
    + rewrite iS; apply incl_trans with (2 := HF0 _ IHn), HF2.
  Qed.

  Let gfp_sym : sym gfp ⊆ gfp.
  Proof. intros ? ? H ?; apply i_sym, H. Qed.

  Hypothesis HF3 : forall R, F R o F R ⊆ F (R o R).   (* Transitivity *)

  Let i_trans n : i n o i n ⊆ i n.
  Proof.
    induction n as [ | n IHn ].
    + rewrite i0; auto.
    + rewrite iS; apply incl_trans with (1 := @HF3 _), HF0, IHn.
  Qed.

  Let gfp_trans : gfp o gfp ⊆ gfp.
  Proof.
    intros ? ? H ?; apply i_trans.
    revert H; apply comp_mono; auto.
  Qed.

  Fact gfp_equiv : equiv _ gfp.
  Proof.
    msplit 2.
    + intro; apply gfp_refl; auto.
    + intros ? y ? ? ?; apply gfp_trans; exists y; auto.
    + intros ? ?; apply gfp_sym.
  Qed.

  Fact gfp_greatest R : R ⊆ F R -> R ⊆ gfp.
  Proof.
    intros HR x y H n; revert x y H.
    induction n as [ | n IHn ].
    + now auto.
    + apply incl_trans with (1 := HR).
      rewrite iS; apply HF0; auto.
  Qed. 

  Let gfp_fix1 : F gfp ⊆ gfp.
  Proof.
    intros ? ? H ?.
    apply i_S; rewrite iS.
    revert H; apply HF0; auto.
  Qed.

  (** This is ω-continuity *)

  Definition gfp_continuous := forall (s : nat -> M -> M -> Prop), 
                        (forall n m, n <= m -> s m ⊆ s n) 
                     -> (fun x y => forall n, F (s n) x y) ⊆ F (fun x y => forall n, s n x y).

  Variable HF4 : gfp_continuous. 

  Let gfp_fix0 : gfp ⊆ F gfp.
  Proof.
    intros ? ? H.
    apply HF4; auto.
    intro; rewrite <- iS; apply H.
  Qed.

  Fact gfp_fix x y : F gfp x y <-> gfp x y.
  Proof. split; auto. Qed.

  (** This is for decidability *)

  Let dec R := forall x y, { R x y } + { ~ R x y }.

  Variable HF5 : forall R, dec R -> dec (F R).       (* Preservation of decidability *)

  Let i_dec n : dec (i n).
  Proof.
    induction n as [ | n IHn ].
    + rewrite i0; left; auto.
    + rewrite iS; apply HF5; auto.
  Qed.

  (** For the decidability of gfp, we need the finiteness
      so that gfp = i n for a sufficiently large n *)

  (** A good pair for i (ie n < m and i n ⊆ i m) means gfp is reached  at n *)

  Let i_dup n m : n < m -> i n ⊆ i m -> forall k, n <= k -> forall x y, gfp x y <-> i k x y.
  Proof.
    intros H1 H2.
    generalize (i_decr H1) (i_S n); rewrite iS; intros H3 H4.
    generalize (incl_trans _ _ _ H2 H3); intros H5.
    assert (forall p, i n ⊆ i (p+n)) as H6.
    { induction p as [ | p IHp ]; auto.
      simpl plus; rewrite iS.
      apply incl_trans with (1 := H5), HF0; auto. }
    intros k Hk x y; split; auto.
    intros H a.
    destruct (le_lt_dec a k).
    + revert H; apply i_decr; auto.
    + replace a with (a-n+n) by lia.
      apply H6.
      revert H; apply i_decr; auto.
  Qed.

  (** If there is a good pair below b, then gfp = i b *)

  Let gfp_reached b : (exists n m, n < m <= b /\ i n ⊆ i m) -> (forall x y, gfp x y <-> i b x y).
  Proof.
    intros (n & m & H1 & H2). 
    apply i_dup with (2 := H2); auto; try lia.
  Qed.

  Variable HF6 : finite_t M.     (* Finiteness of the domain *)

  (** When M is finite, there is a list [T1;...;Tk] of relations of
      type M -> M -> Prop which contains every weakly decidable relations 
      upto equivalence. 

      Hence, by the a generalized version of the PHP (proved w/o
      assuming discreteness), for n greater than the length of
      the list for M, one can find a duplicate
      in the list [i 0; ...;i n] ie a < b <= n such
      that i a ~ Tu ~ Tv ~ i b

      Then one can deduce i n ~ gfp *)

  Theorem gfp_finite_t : { n | forall x y, gfp x y <-> i n x y }.
  Proof.
    destruct finite_t_weak_dec_rels with (1 := HF6)
      as (mR & HmR).
    exists (S (length mR)).
    set (l := map i (list_an 0 (S (length mR)))).
    apply (@gfp_reached (S (length mR))).
    destruct php_upto 
      with (R := fun R T => forall x y, R x y <-> T x y)
           (l := l) (m := mR)
      as (a & R & b & T & c & H1 & H2).
    + intros R S H ? ?; rewrite H; tauto.
    + intros R S T H1 H2 ? ?; rewrite H1, H2; tauto.
    + intros R HR.
      unfold l in HR; apply in_map_iff in HR.
      destruct HR as (n & <- & _).
      destruct (HmR (i n)) as (T & H1 & H2).
      * intros x y; destruct (i_dec n x y); tauto.
      * exists T; auto.
    + unfold l; rewrite map_length, list_an_length; auto.
    + unfold l in H1; apply map_duplicate_inv in H1.
      destruct H1 as (a' & n & b' & m & c' & H1 & H3 & H4 & H5 & H6 & H7).
      exists n, m; rewrite <- H3, <- H5; split; try (intros ? ?; apply H2).
      apply list_an_duplicate_inv in H7; lia.
  Qed.

  (** As a consequence of been reached after a finite number of steps, 
      gfp is one of the i n (for some computable n) and thus decidable *)

  Theorem gfp_decidable : dec gfp.
  Proof.
    destruct gfp_finite_t as (n & Hn).
    intros x y; destruct (i_dec n x y); [ left | right ]; 
      rewrite Hn; tauto.
  Qed.
  
End gfp.