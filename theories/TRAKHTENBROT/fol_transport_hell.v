(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Lia Eqdep_dec.

From Undecidability.Shared.Libs.DLW.Utils
  Require Import utils_tac utils_list finite.

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

From Undecidability.TRAKHTENBROT
  Require Import notations fol_ops fo_terms fo_logic.

Set Implicit Arguments.

Notation ø := vec_nil.

Opaque fo_term_subst fo_term_map fo_term_sem.

(** Transport between isomorphic signatures is TRANSPORT HELL 


    One should restudy those proof to extract generalize
    eq_rect commutation and eq_rect composition result
    so as to be able to pass transport hell

**)

Section fo_term_map_ar.

  Variable (X S : Type) (f g : S -> nat) (Efg : forall s, f s = g s).

  Let new Y (mr : forall s, vec Y (f s) -> Y) : forall s, vec Y (g s) -> Y.
  Proof. intros s; rewrite <- Efg; apply mr. Defined.  

  Let R (s : fo_term X f) (t : fo_term X g) : Prop :=
       forall Y mr i, fo_term_sem mr i s = fo_term_sem (@new Y mr) i t.

  Fact toto1 Y a b (mr : vec Y a -> Y) (E : a = b) :
        eq_rect _ (fun n => vec Y n -> Y) mr _ E = fun v => mr (eq_rect_r _ v E).
  Proof. subst; auto. Qed.

  Fact toto2 Y Z h a b v (E : a = b) :  eq_rect _ (vec Z) (vec_map h v) _ E
                                     = @vec_map Y Z h _ (eq_rect _ (vec Y) v _ E).
  Proof. subst; auto. Qed.

  Fact toto3 Y a b (h : pos a -> Y) (E : a = b) :  eq_rect _ (vec Y) (vec_set_pos h) _ E
                                     = vec_set_pos (eq_rect _ (fun n => pos n -> Y) h _ E).
  Proof. subst; auto. Qed.

  Fact toto4  Y a b (h : pos a -> Y) (E : a = b) x : eq_rect _ (fun n => pos n -> Y) h _ E x
                                                  = h (eq_rect_r _ x E).
  Proof. subst; auto. Qed.

  Definition fo_term_map_ar (s : fo_term X f) : sig (R s).
  Proof.
    induction s as [ x | s v IHv ] using fo_term_pos_rect.
    + exists (in_var x); intros Y mr i; rew fot; auto.
    + apply pos_reif_t in IHv; destruct IHv as (w & Hw).
      set (k := fun q => w (eq_rect_r _ q (Efg s))).
      exists (in_fot s (vec_set_pos k)).
      intros Y mr i; rew fot; unfold new.
      rewrite toto1; f_equal.
      unfold eq_rect_r.
      rewrite toto2, toto3.
      apply vec_pos_ext; intros p.
      do 2 rewrite vec_pos_map.
      rewrite vec_pos_set; simpl.
      unfold k; rewrite toto4.
      unfold R in Hw; rewrite Hw.
      f_equal; f_equal.
      generalize (Efg s).
      intros []; auto.
  Qed.

End fo_term_map_ar.

Fact eq_nat_pirr (n : nat) (H : n = n ) : H = eq_refl.
Proof. apply UIP_dec, eq_nat_dec. Qed.

Section signature_transport.

  (** To signatures in computable one-to-one correspondance *)

  Variable (Σ Σ' : fo_signature)
           (i_t : syms Σ -> syms Σ') (j_t : syms Σ' -> syms Σ) 
           (i_t_ar : forall s, ar_syms Σ' (i_t s) = ar_syms Σ s)
           (ij_t : forall s, i_t (j_t s) = s) (ji_t : forall s, j_t (i_t s) = s)
           (i_r : rels Σ -> rels Σ') (j_r : rels Σ' -> rels Σ)
           (i_r_ar : forall s, ar_rels Σ' (i_r s) = ar_rels Σ s)
           (ij_r : forall s, i_r (j_r s) = s) (ji_r : forall s, j_r (i_r s) = s).

  Definition fom_map_sig X : fo_model Σ X -> fo_model Σ' X.
  Proof.
    intros [ syms rels ].
    exists.
    + intros s.
      rewrite <- (ij_t s), i_t_ar.
      apply (syms (j_t s)).
    + intros r.
      rewrite <- (ij_r r), i_r_ar.
      apply (rels (j_r r)).
  Defined.

  Arguments fom_map_sig X M /.

  Fact toto5 Y K (f : K -> nat) a b (m : vec Y (f a) -> Y) (E : a = b) :
       eq_rect _ (fun s => vec Y (f s) -> Y) (fun v => m v) _ E
      = fun v : vec Y (f b) => m (eq_rect_r (fun s => vec Y (f s)) v E).
  Proof. subst; auto. Qed.

  Fact toto6 Y K (f : K -> nat) Z h a b v (E : a = b) :  eq_rect _ (fun k => vec Z (f k)) (vec_map h v) _ E
                                     = @vec_map Y Z h _ (eq_rect _ (fun k => vec Y (f k)) v _ E).
  Proof. subst; auto. Qed.


  Fact toto7 S K (P : S -> Type) (ms : forall s, P s -> K) a b v (E : a = b) :
              ms a v = ms b (eq_rect _ P v _ E).
  Proof. subst; auto. Qed.

  Fact eq_rect_comm X (P Q : X -> Type) (f : forall x : X, P x -> Q x) (a b : X) (E : a = b) (x : P a) :
                   eq_rect _ Q (f _ x) _ E = f _ (eq_rect _ P x _ E).
  Proof. subst; auto. Qed. 

  (*  The problem is to find general enough rewriting rules
      so that you can apply them any many cases

          a = f b          b = c
      P a -------> P (f b) -----> P (f c)


                 a = f c
            P a  -----> P (f c)  

       The proof is ALWAYS trivial

   *)

  Fact eq_comp X Y (P : Y -> Type) (f : X -> Y) a b c (E1 : a = f b) (E2 : b = c) t :
             eq_rect _ (fun x => P (f x)) (eq_rect _ P t _ E1) _ E2
           = eq_rect _ P t _ (eq_rect _ (fun y => a = f y) E1 _ E2).
  Proof. subst; auto. Qed. 

  (*          a =  b            f b = k
      P (f a) -------> P (f b) -------> P k

                     f a = k
             P (f a) --------> P k  *)

  Fact eq_comp' X Y (P : Y -> Type) (f : X -> Y) a b c (E1 : a = b) (E2 : f b = c) t :
             eq_rect _ P (eq_rect _ (fun n => P (f n)) t _ E1) _ E2
           = eq_rect _ P t _ (eq_rect_r (fun y => f y = c) E2 E1).
  Proof. subst; auto. Qed. 

  Fact eq_comm X  Y (P : X -> Type) a b (h : P a -> Y) (x : P b) (E : a = b) :
           eq_rect _ (fun n => P n -> Y) h _ E x = h (eq_rect_r P x E).
  Proof. subst; auto. Qed. 

  Section terms.

  Variable X : Type.

  Let T := fo_term X (ar_syms Σ).
  Let T' := fo_term X (ar_syms Σ').

  Let R1 (s : T) (t : T') : Prop := 
    forall Y M φ, fo_term_sem (fom_syms M) φ s 
              = fo_term_sem (fom_syms (@fom_map_sig Y M)) φ t.

  Definition fo_term_map_sig (s : T) : sig (R1 s).
  Proof.
    induction s as [ x | s v IHv ] using fo_term_pos_rect.
    + exists (in_var x); intros Y [ syms ? ] phi; simpl; rew fot; auto.
    + change (vec T (ar_syms Σ s)) in v.
      apply pos_reif_t in IHv; destruct IHv as (f & Hf).
      exists (in_fot (i_t s) (vec_set_pos (fun q => f (eq_rect _ _ q _ (i_t_ar s))))).
      intros Y [ ms mr ] psi; unfold fom_map_sig; rew fot; simpl.
      fold T'; fold T.
      unfold eq_rect_r.
      rewrite toto1.
      rewrite toto5.
      unfold eq_rect_r.
      rewrite toto7 with (ms := ms) (E := ji_t s).
      f_equal.
      rewrite toto6, toto2, toto6.
      apply vec_pos_ext; intros; repeat rewrite vec_pos_map.
      rewrite eq_rect_comm 
            with (f := fun n => @vec_set_pos _ (ar_syms _ n)).
      rewrite eq_rect_comm 
            with (f := fun n => @vec_set_pos _ n).
      rewrite eq_rect_comm 
            with (f := fun n => @vec_set_pos _ (ar_syms _ n)).
      rewrite vec_pos_set.
      specialize (Hf p _ (Mk_fo_model _ ms mr) psi); simpl in Hf.
      fold T in Hf; rewrite Hf.
      f_equal; simpl.
      repeat rewrite eq_comm.
      f_equal.
      clear Hf.
      unfold eq_rect_r.
      do 2 rewrite eq_sym_involutive.
      do 2 rewrite eq_comp'.
      unfold eq_rect_r.
      rewrite eq_comp.
      match goal with
        |- ?p = eq_rect ?n _ ?p ?n ?e => generalize e
      end; intros e. 
      rewrite eq_nat_pirr with (H := e); auto.
  Qed.

  End terms.

  Check fo_term_map_sig.

  Let F := fol_form Σ.
  Let F' := fol_form Σ'.

  Let R2 (A : F) (B : F') : Prop := 
    forall X M φ, fol_sem M φ A <-> fol_sem (@fom_map_sig X M) φ B.

  Definition fol_map_sig_full A : sig (R2 A).
  Proof.
    induction A as [ | r v | b A [ A' HA ] B [ B' HB ] | q A [ A' HA ] ].
    + exists ⊥; intros X M phi; simpl; tauto.
    + generalize (fun p => fo_term_map_sig (vec_pos v p)); intros w.
      apply pos_reif_t in w.
      destruct w as (w & Hw).
      exists (fol_atom _ (i_r r) (eq_rect_r _ (vec_set_pos w) (i_r_ar r))).
      intros X M phi.
      specialize (fun p => Hw p X M phi).
      destruct M as [ ms mr ]; simpl in *.
      match goal with |- ?a <-> ?b => cut (a=b); [ intros ->; tauto | ] end.
      unfold eq_rect_r.
      do 2 rewrite eq_comm.
      unfold eq_rect_r.
      rewrite eq_comp'.
      unfold eq_rect_r.
      do 2 rewrite eq_sym_involutive.
      rewrite toto2.
      rewrite toto7 with (E := ji_r r).
      rewrite toto6.
      f_equal.
      apply vec_pos_ext; intros p.
      do 2 rewrite vec_pos_map.
      rewrite (Hw p).
      unfold eq_rect_r; f_equal.
      do 2 rewrite eq_comp.
      rewrite eq_rect_comm 
            with (f := fun n => @vec_set_pos _ n).
      rewrite vec_pos_set.
      rewrite eq_comm; f_equal.
      unfold eq_rect_r.
      match goal with
        |- ?p = eq_rect ?n _ ?p ?n ?e => generalize e
      end; intros e. 
      rewrite eq_nat_pirr with (H := e); auto.
    + exists (fol_bin b A' B'); intros X M phi.
      specialize (HA X M phi).
      specialize (HB X M phi).
      apply fol_bin_sem_ext; auto.
    + exists (fol_quant q A'); intros X M phi.
      apply fol_quant_sem_ext; intros x.
      specialize (HA X M (phi↑x)); auto.
  Qed.

  Definition fol_map_sig A := proj1_sig (fol_map_sig_full A).

  Theorem fol_map_signature X M φ A :
           fol_sem M φ A <-> fol_sem (@fom_map_sig X M) φ (fol_map_sig A).
  Proof. apply (proj2_sig (fol_map_sig_full A)). Qed.

End signature_transport.

Check fol_map_signature.
Print Assumptions fol_map_signature.
