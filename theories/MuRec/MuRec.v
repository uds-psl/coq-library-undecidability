Require Import Arith Lia List Bool Eqdep_dec .

From Undecidability.Shared.Libs.DLW 
  Require Import utils_tac utils_nat utils_list finite pos vec.

Set Implicit Arguments.

Set Default Proof Using "Type".

Local Reserved Notation " '[|' f '|]' " (at level 0).
Local Reserved Notation "'⟦' f '⟧'".

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

Reserved Notation "  '[' f ';' v ']' '▹' x " (at level 70).

Inductive ra_bs : forall k, recalg k -> vec nat k -> nat -> Prop :=
    | in_ra_bs_cst  : forall n v,             [ra_cst n;        v] ▹ n
    | in_ra_bs_zero : forall v,               [ra_zero;         v] ▹ 0
    | in_ra_bs_succ : forall v,               [ra_succ;         v] ▹ S (vec_head v)
    | in_ra_bs_proj : forall k v j,           [@ra_proj k j;    v] ▹ vec_pos v j
    
    | in_ra_bs_comp : forall k i f (gj : vec (recalg i) k) v w x,
                                   (forall j, [vec_pos gj j;    v] ▹ vec_pos w j)
                               ->             [f;               w] ▹ x
                               ->             [ra_comp f gj;    v] ▹ x

    | in_ra_bs_rec_0 : forall k f (g : recalg (S (S k))) v x,
                                              [f;               v] ▹ x
                               ->             [ra_rec f g;   0##v] ▹ x

    | in_ra_bs_rec_S : forall k f (g : recalg (S (S k))) v n x y,
                                              [ra_rec f g;   n##v] ▹ x
                               ->             [g;         n##x##v] ▹ y
                               ->             [ra_rec f g; S n##v] ▹ y
                               
    | in_ra_bs_min : forall k (f : recalg (S k)) v x w ,
                           (forall j : pos x, [f;    pos2nat j##v] ▹ S (vec_pos w j))
                               ->             [f;            x##v] ▹ 0
                               ->             [ra_min f;        v] ▹ x
where " [ f ; v ] ▹ x " := (@ra_bs _ f v x).

Definition Halt_murec (a : { n : nat & recalg n & Vector.t nat n }) : Prop :=
    let (n, f, v) := a in exists x, [f ; v ] ▹ x.