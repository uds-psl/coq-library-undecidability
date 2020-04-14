(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Eqdep_dec Omega List Bool.

From Undecidability.Shared.Libs.DLW.Utils 
  Require Import utils_tac utils_nat utils_list finite. 

From Undecidability.Shared.Libs.DLW.Vec 
  Require Import pos vec.

Set Implicit Arguments.

Local Reserved Notation " '[|' f '|]' " (at level 0).
Local Reserved Notation "'⟦' f '⟧'".

Section Recursive_algorithms.

  Unset Elimination Schemes.

  Inductive recalg : nat -> Type :=
    | ra_cst  : nat -> recalg 0
    | ra_zero : recalg 1
    | ra_succ : recalg 1
    | ra_proj : forall k, pos k -> recalg k
    | ra_comp : forall k i, recalg k -> vec (recalg i) k -> recalg i
    | ra_rec  : forall k, recalg k -> recalg (S (S k)) -> recalg (S k)
    | ra_min  : forall k, recalg (S k) -> recalg k
    .

  Set Elimination Schemes.

  Section recalg_rect.

    Variable P : forall k, recalg k -> Type.

    Hypothesis Pcst  : forall n, P (ra_cst n).
    Hypothesis Pzero : P ra_zero.
    Hypothesis Psucc : P ra_succ.
    Hypothesis Pproj : forall k p, P (@ra_proj k p).
    Hypothesis Pcomp : forall k i f gj, P f -> (forall p, @P i (@vec_pos _ k gj p)) 
                                     -> P (ra_comp f gj).
    Hypothesis Prec  : forall k f g, @P k f -> P g -> P (ra_rec f g).
    Hypothesis Pmin  : forall k f, @P (S k) f -> P (ra_min f).

    Fixpoint recalg_rect k f { struct f } : @P k f :=
      match f with
        | ra_cst n     => Pcst n
        | ra_zero      => Pzero
        | ra_succ      => Psucc
        | ra_proj p    => Pproj p 
        | ra_comp f gj => Pcomp _ [|f|] (fun p => [|vec_pos gj p|])
        | ra_rec f g   => Prec [|f|] [|g|]
        | ra_min f     => Pmin [|f|]
      end
    where "[| f |]" := (@recalg_rect _ f).

  End recalg_rect.

  Definition recalg_rec (P : forall k, recalg k -> Set) := recalg_rect P.
  Definition recalg_ind (P : forall k, recalg k -> Prop) := recalg_rect P.

  Section recalg_rec_type.

    Variables (X : Type) (P : nat -> Type).
    Hypothesis Pcst  : P 0.
    Hypothesis Pzero : P 1.
    Hypothesis Psucc : P 1.
    Hypothesis Pproj : forall k (p : pos k), P k.
    Hypothesis Pcomp : forall k i, P k -> vec (P i) k -> P i. 
    Hypothesis Prec  : forall k, P k -> P (S (S k)) -> P (S k).
    Hypothesis Pmin  : forall k, P (S k) -> P k.

    Fixpoint recalg_rec_type k (f : recalg k) { struct f } : P k :=
      match f in recalg i return P i with
        | ra_cst n     => Pcst
        | ra_zero      => Pzero
        | ra_succ      => Psucc
        | ra_proj p    => Pproj p 
        | ra_comp f gj => Pcomp [|f|] (vec_map (fun f => @recalg_rec_type _ f) gj)
        | ra_rec f g   => Prec [|f|] [|g|]
        | ra_min f     => Pmin [|f|]
      end
    where "[| f |]" := (@recalg_rec_type _ f).

  End recalg_rec_type.

  Definition ra_size k : recalg k -> nat.
  Proof.
    induction 1 as [ | | | | k i Hf Hg | k Hf Hg | k Hf ]
      using recalg_rec_type.
    + exact 1.
    + exact 1.
    + exact 1.
    + exact 1.
    + exact (1+Hf+vec_sum Hg).
    + exact (1+Hf+Hg).
    + exact (1+Hf).
  Defined. 
  
  Section recalg_inj.
 
    (* Injectivity is not a given for dependently typed constructors but it holds
       when the dependent parameter is from a set (ie a Type with decidable equality *)
  
    Let nat_dep_inj (P : nat -> Type) n x y : existT P n x = existT P n y -> x = y.
    Proof. apply inj_pair2_eq_dec, eq_nat_dec. Qed.
    
    Local Ltac inj := let H := fresh in intros H; injection H; clear H; auto.
    
    Local Ltac diauto := 
      repeat match goal with 
        H: existT _ _ _ = existT _ _ _ |- _ => apply nat_dep_inj in H 
      end; auto.
      
    Fact ra_cst_inj n m : ra_cst n = ra_cst m -> n = m.
    Proof. inj. Qed.

    Fact ra_proj_inj k (p q : pos k) : ra_proj p = ra_proj q -> p = q.
    Proof. inj. Qed.
    
    (* This one is more subtle and requires type casts *)

    Fact ra_comp_inj k k' i f f' gj gj' : 
         @ra_comp k i f gj = @ra_comp k' i f' gj'
      -> exists H : k = k', eq_rect _ _ f _ H = f'
                         /\ eq_rect _ _ gj _ H = gj'.
    Proof.
      inj; intros ? ? H; exists H; subst; simpl; diauto.
    Qed.
 
    Fact ra_rec_inj k f g f' g' : @ra_rec k f g = ra_rec f' g' -> f = f' /\ g = g'.
    Proof.
      inj; intros; diauto.
    Qed.

    Fact ra_min_inj k f f' : @ra_min k f = ra_min f' -> f = f'.
    Proof.
      inj; intros; diauto.
    Qed.

  End recalg_inj.

End Recursive_algorithms.

Definition functional X Y (f : X -> Y -> Prop) := forall x y1 y2, f x y1 -> f x y2 -> y1 = y2.
Definition total X Y (f : X -> Y -> Prop) := forall x, exists y, f x y.

Section recursor.

  Variables (F : nat -> Prop) (G : nat -> nat -> nat -> Prop).
  
  Fixpoint μ_rec n := 
    match n with
      | 0   => F
      | S n => fun x => exists y, μ_rec n y /\ G n y x
      end.

  Fact μ_rec_inv n x : μ_rec n x -> exists s, F (s 0) 
                                           /\ s n = x
                                           /\ forall i, i < n -> G i (s i) (s (S i)).
  Proof.
    revert x; induction n as [ | n IHn ]; intros x; simpl.
    + exists (fun _ => x); msplit 2; auto; intros; omega.
    + intros (y & H1 & H2).
      destruct (IHn _ H1) as (s & H3 & H4 & H5).
      exists (fun i => if le_lt_dec (S n) i then x else s i); msplit 2; auto.
      * destruct (le_lt_dec (S n) (S n)); auto; omega.
      * intros i Hi.
        destruct (le_lt_dec (S n) i); destruct (le_lt_dec (S n) (S i)); auto; try omega.
        - replace i with n by omega.
          rewrite H4; auto.
        - apply H5; omega.
  Qed.

  Theorem μ_rec_eq n x : μ_rec n x <-> exists s, F (s 0) 
                                              /\ s n = x
                                              /\ forall i, i < n -> G i (s i) (s (S i)).
  Proof.
    split.
    + apply μ_rec_inv.
    + intros (s & H1 & H2 & H3).
      rewrite <- H2; clear x H2.
      revert s H1 H3.
      induction n as [ | n IHn ]; intros s H1 H2; simpl; auto.
      exists (s n); split; auto.
  Qed.

  Hypothesis (Ffun : forall n m, F n -> F m -> n = m) 
             (Gfun : forall x y n m, G x y n -> G x y m -> n = m).

  Fact μ_rec_fun : functional μ_rec. 
  Proof.
    intros n; induction n as [ | n IHn ]; simpl; auto.
    intros x y (a & H1 & H2) (b & H3 & H4).
    specialize (IHn _ _ H1 H3); subst b.
    revert H2 H4; apply Gfun.
  Qed.
 
End recursor.

Section minimization.

  Variables (R : nat -> nat -> Prop)
            (Rfun : forall n u v, R n u -> R n v -> u = v).

  Definition μ_min n := R n 0 /\ forall i, i < n -> exists u, R i (S u).
 
  Fact μ_min_eq n : μ_min n <-> R n 0 /\ exists s, forall i, i < n -> R i (S (s i)).
  Proof.
    unfold μ_min; split; intros [ H0 H ]; split; auto.
    + apply fin_reif_nat with (1 := H).
    + clear H0; destruct H as (s & Hs).
      intros i ?; exists (s i); auto.
  Qed.

  Fact μ_min_fun n m : μ_min n -> μ_min m -> n = m.
  Proof.
    intros (H1 & H2) (H3 & H4).
    destruct (lt_eq_lt_dec n m) as [ [ H | ] | H ]; auto; 
      [ apply H4 in H | apply H2 in H ]; destruct H as (u & Hu);
      [ generalize (Rfun H1 Hu) | generalize (Rfun H3 Hu) ]; discriminate.
  Qed. 

  Hypothesis HR : forall x, exists y, R x y.

  Fact μ_min_of_total : (exists n, μ_min n) <-> exists x, R x 0.
  Proof.
    split.
    + intros (n & ? & _); exists n; auto.
    + intros H.
      destruct first_which_ni with (2 := H) as (n & H1 & H2).
      * intros n; destruct (HR n) as ([ | k] & Hk); auto.
        right; intros C; generalize (Rfun Hk C); discriminate.
      * exists n; split; auto.
        intros i Hi; apply H2 in Hi.
        destruct (HR i) as ([ | k] & Hk); try tauto.
        exists k; auto.
  Qed.

End minimization.

Section relational_semantics.

  (* Recursive functions can be interpreted in Coq as (functional) relations *)

  Notation natfun := (fun k => vec nat k -> nat -> Prop).

  Section defs.

    Definition s_cst c : natfun 0 := fun _ x => x=c.
    Definition s_zero  : natfun 1 := fun _ x => x=0.
    Definition s_succ  : natfun 1 := fun v x => x=S (vec_head v).
    Definition s_proj k (p : pos k) : natfun k := fun v x => vec_pos v p = x.

    Variable k i : nat.
    
    Implicit Types (f : natfun k) (g : natfun (S k)) (h : natfun (S (S k))) (gj : vec (natfun i) k).

    Definition s_comp f gj : natfun i := fun v x => exists gl, f gl x /\ forall p, vec_pos gj p v (vec_pos gl p).
      
    (** the recursor s_rec_r f h n v x 
                 <-> exists x0,...,xn,  f      v  x0,
                                        h (0##x0##v) x1,
                                        h (1##x1##v) x2,
                                        ...
                                        h (.##..##v) xn, 
                                    and xn = x 
    **)
   
    Definition s_rec f h v := μ_rec (f (vec_tail v)) (fun x y => h (x##y##vec_tail v)) (vec_head v).

    Theorem s_rec_eq f h v x : s_rec f h v x <-> exists s, f (vec_tail v) (s 0) 
                                                        /\ s (vec_head v) = x
                                                        /\ forall i, i < vec_head v -> h (i##s i##vec_tail v) (s (S i)).
    Proof. vec split v with n; apply μ_rec_eq. Qed.

    Definition s_min g v := μ_min (fun n => g (n##v)).

  End defs.
  
  (** we define the semantics of a recursive algorithm of arity k 
      which is a relation vec nat k -> nat -> Prop, obviously functional (see below)
      We interpret the constants ra_* with the corresponding s_* operator on relations
   **) 

  Definition ra_rel : forall k, recalg k -> natfun k.
  Proof.
    apply recalg_rect with (P := fun k _ => natfun k).
    exact s_cst.
    exact s_zero.
    exact s_succ.
    exact s_proj.
    intros ? ? ? ? hf hgj; exact (s_comp hf (vec_set_pos hgj)).
    intros ? ? ? hf hg; exact (s_rec hf hg).
    intros ? ? hf; exact (s_min hf).
  Defined.
  
  Notation "[| f |]" := (@ra_rel _ f) (at level 0).
 
  Fact ra_rel_fix_cst i :         [| ra_cst i     |]      = s_cst i.                   Proof. reflexivity. Qed.
  Fact ra_rel_fix_zero :          [| ra_zero      |]      = s_zero.                    Proof. reflexivity. Qed.
  Fact ra_rel_fix_succ :          [| ra_succ      |]      = s_succ.                    Proof. reflexivity. Qed.
  Fact ra_rel_fix_proj k p :      [| @ra_proj k p |]      = s_proj p.                  Proof. reflexivity. Qed.
  Fact ra_rel_fix_rec k f g :     [| @ra_rec k f g |]     = s_rec [|f|] [|g|].         Proof. reflexivity. Qed.
  Fact ra_rel_fix_min k f :       [| @ra_min k f |]       = s_min [|f|].               Proof. reflexivity. Qed.
  Fact ra_rel_fix_comp k i f gj : [| @ra_comp k i f gj |] = s_comp [|f|] (vec_map (fun x => [|x|]) gj).
  Proof.
    simpl ra_rel; f_equal.
    apply vec_pos_ext; intros p.
    rewrite vec_pos_set, vec_pos_map; trivial.
  Qed.
 
  Section functional.

    Lemma s_cst_fun c : functional (s_cst c).
    Proof. intros v x y Hx Hy; rewrite Hy; trivial. Qed.

    Lemma s_zero_fun : functional s_zero.
    Proof. intros v x y Hx Hy; rewrite Hy; trivial. Qed.

    Lemma s_succ_fun : functional s_succ.
    Proof. intros v x y Hx Hy; rewrite Hy; trivial. Qed.
    
    Lemma s_proj_fun k p : functional (@s_proj k p).
    Proof.
      intros v x y Hx Hy.
      red in Hx, Hy. 
      rewrite <- Hx.
      trivial.
    Qed.

    Variable k i : nat.
    Implicit Types (f : natfun k) (gj : vec (natfun i) k) (g : natfun (S k)) (h : natfun (S (S k))).

    Lemma s_comp_fun f gj : functional f -> (forall p, functional (vec_pos gj p)) -> functional (s_comp f gj).   
    Proof.
      intros f_fun gj_fun v x y [ gx [ Hx1 Hx2 ] ] [ gy [ Hy1 Hy2 ] ].
      replace gx with gy in Hx1.
      + apply (@f_fun gy); trivial.
      + apply vec_pos_ext.
        intros p; apply (gj_fun p v); auto.
    Qed.

    Lemma s_rec_fun f h : functional f -> functional h -> functional (s_rec f h).
    Proof.
      intros Hf Hh ? ? ?. 
      apply μ_rec_fun. 
      + apply Hf.
      + intros ? ? ? ? ?; apply Hh; auto.
    Qed.

    Lemma s_min_fun g : functional g -> functional (s_min g).
    Proof.
      intros Hg ? ? ?; apply μ_min_fun.
      intros ? ? ?; apply Hg.
    Qed.

  End functional.

  Hint Resolve s_cst_fun s_zero_fun s_succ_fun s_proj_fun s_rec_fun s_min_fun : core.

  (* [| f |] is a functional/deterministic relation *)

  Theorem ra_rel_fun k (f : recalg k) v x y : [|f|] v x -> [|f|] v y -> x = y.
  Proof.
    revert v x y; change (functional [|f|]).
    induction f; try (simpl; auto; fail).
    rewrite ra_rel_fix_comp.
    apply s_comp_fun; auto. 
    intro; rewrite vec_pos_map; auto.
  Qed.

  Section total.

    Fact ra_cst_tot n : total [| ra_cst n |].
    Proof. intros ?; exists n; simpl; red; auto. Qed.

    Fact ra_zero_tot : total [| ra_zero |].
    Proof. intros ?; exists 0; simpl; red; auto. Qed.

    Fact ra_succ_tot : total [| ra_succ |].
    Proof. intros v; exists (S (vec_head v)); simpl; red; auto. Qed.
  
    Fact ra_proj_tot n p : total [| @ra_proj n p |].
    Proof. intros v; exists (vec_pos v p); simpl; red; auto. Qed.

    Fact ra_rec_tot n f g : total [|f|] -> total [|g|] -> total [|@ra_rec n f g|].
    Proof.
      intros Hf Hg v; vec split v with x.
      simpl; induction x as [ | x IHx ]; simpl.
      + destruct (Hf v) as (y & Hy).
        exists y; red; simpl; auto.
      + destruct IHx as (y & Hy).
        destruct (Hg (x##y##v)) as (z & Hz).
        exists z, y; simpl; split; auto.
    Qed.

    Variables (k i : nat) (f : recalg k) (g : vec (recalg i) k)
              (Hf : total [|f|]) (Hg : forall p, total [|vec_pos g p|]).

    Fact ra_comp_tot : total [|ra_comp f g|].
    Proof.
      intros v.
      assert (H1 : forall p, exists x, [|vec_pos g p|] v x) by (intro; apply Hg).
      apply vec_reif in H1; destruct H1 as (w & Hw).
      destruct (Hf w) as (y & Hy).
      exists y, w; split; auto.
      intro; rewrite vec_pos_set; auto.
    Qed.

  End total.

  Section prim_rec.

    Definition prim_rec : forall n, recalg n -> Prop.
    Proof.
      apply recalg_rect.
      + intros; exact True.
      + exact True.
      + exact True.
      + intros; exact True.
      + intros k i _ _ H1 H2; exact (H1 /\ forall p, H2 p).
      + intros k _ _ H1 H2; exact (H1 /\ H2).
      + intros; exact False.
    Defined. 

    Definition prim_rec_bool : forall n, recalg n -> bool.
    Proof.
      apply recalg_rect.
      + intros; exact true.
      + exact true.
      + exact true.
      + intros; exact true.
      + intros k i _ _ H1 H2.
        exact (andb H1 (fold_right andb true (map H2 (pos_list _)))).
      + intros k _ _ H1 H2; exact (andb H1 H2).
      + intros; exact false.
    Defined. 

    Let fold_right_andb l : fold_right andb true l = true <-> forall x, In x l -> x = true.
    Proof.
      induction l as [ | x l IHl ]; simpl; try tauto.
      rewrite andb_true_iff, IHl; firstorder; subst; auto.
    Qed.

    Fact prim_rec_bool_spec n f : @prim_rec_bool n f = true <-> prim_rec f.
    Proof.
      induction f as [ x | | | n p | n i f g Hf Hg | n f g Hf Hg | n f Hf ]; simpl; try tauto.
      + rewrite andb_true_iff, fold_right_andb, <- Forall_forall.
        rewrite Forall_map, Forall_forall, Hf.
        split; intros (? & H); split; auto.
        * intros p; apply Hg, H, pos_list_prop.
        * intros x Hx; apply Hg, H.
      + rewrite andb_true_iff, Hf, Hg; tauto.
      + split; try tauto; discriminate.
    Qed.

    Hint Resolve ra_cst_tot ra_zero_tot ra_succ_tot ra_proj_tot ra_rec_tot : core.

    Fact prim_rec_tot k f : @prim_rec k f -> total [|f|].
    Proof.
      induction f as [ x | | | n p | n i f g Hf Hg | n f g Hf Hg | n f Hf ]; intros H; simpl in H; auto.
      + apply ra_comp_tot; try tauto; intros; apply Hg, H.
      + apply ra_rec_tot; tauto.
      + tauto.
    Qed.

  End prim_rec.

End relational_semantics.

Arguments s_zero v x /.
Arguments s_cst c v x /.
Arguments s_proj {k} p v x /.
Arguments s_succ v x /.

Definition MUREC_PROBLEM := recalg 0.
Definition MUREC_HALTING : MUREC_PROBLEM -> Prop.
Proof. intros f; exact (ex (ra_rel f vec_nil)). Defined.

