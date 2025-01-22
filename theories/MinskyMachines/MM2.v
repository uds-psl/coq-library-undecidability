(* 
  Author(s):
    Dominique Larchey-Wendling (1)
    Andrej Dudenhefner (2)
  Affiliation(s):
    (1) LORIA -- CNRS
    (2) TU Dortmund University, Dortmund, Germany
*)

(* 
  Problem(s):
    Two-counter Machine Halting (MM2_HALTING)
    Two-counter Machine Halting starting from (0, 0) (MM2_ZERO_HALTING)
    Two-counter Machine Halting ending in (0, 0) (MM2_HALTS_ON_ZERO)
    Two-counter Machine Reversibility (MM2_REV)
    Reversible Two-counter Machine Halting (MM2_REV_HALT)
    Two-counter Machine Uniform Boundedness (MM2_UBOUNDED)
    Two-counter Machine Uniform Mortality (MM2_UMORTAL)
*)

(* 
  Literature:
  [1] Certified Undecidability of Intuitionistic Linear Logic via Binary Stack Machines and Minsky Machines.
      Yannick Forster and Dominique Larchey-Wendling. CPP '19. http://uds-psl.github.io/ill-undecidability/ 
*)

From Stdlib Require Import List Relations.Relation_Operators.

#[local] Set Implicit Arguments.

(* Two counters Minsky machines. Counters are named A and B

    For instructions: INC{A,B} | DEC{A,B} j 

    j is a conditional jump PC index which occurs
    when the counter has non-zero value 
*)

Inductive mm2_instr : Set :=
  | mm2_inc_a : mm2_instr
  | mm2_inc_b : mm2_instr
  | mm2_dec_a : nat -> mm2_instr
  | mm2_dec_b : nat -> mm2_instr.

Reserved Notation "i '//' r '⇢' s" (at level 70, no associativity).
Reserved Notation "P '//' r '→' s" (at level 70, no associativity).
Reserved Notation "P '//' r '↠' s" (at level 70, no associativity).
#[warning="-postfix-notation-not-level-1"]
  Reserved Notation "P '//' r ↓" (at level 70, no associativity).

#[local] Notation mm2_state := (nat*(nat*nat))%type.

(* Instruction step semantics:

    ρ // x ⇢ y : instruction ρ transforms state x into state y 

    Notice that the jump occurs on the non-zero case when DEC

  *)

Inductive mm2_atom : mm2_instr -> mm2_state -> mm2_state -> Prop :=
  | in_mm2s_inc_a  : forall i   a b, mm2_inc_a   // (i,(  a,  b)) ⇢ (1+i,(S a,  b))
  | in_mm2s_inc_b  : forall i   a b, mm2_inc_b   // (i,(  a,  b)) ⇢ (1+i,(  a,S b))
  | in_mm2s_dec_aS : forall i j a b, mm2_dec_a j // (i,(S a,  b)) ⇢ (  j,(  a,  b))
  | in_mm2s_dec_bS : forall i j a b, mm2_dec_b j // (i,(  a,S b)) ⇢ (  j,(  a,  b))
  | in_mm2s_dec_a0 : forall i j   b, mm2_dec_a j // (i,(  0,  b)) ⇢ (1+i,(  0,  b))
  | in_mm2s_dec_b0 : forall i j a,   mm2_dec_b j // (i,(  a,  0)) ⇢ (1+i,(  a,  0))
where "ρ // x ⇢ y" := (mm2_atom ρ x y).

(* instruction ρ occurs at PC index i in the program (1,P) *)

Definition mm2_instr_at (ρ : mm2_instr) i P := exists l r, P = l++ρ::r /\ 1+length l = i.

(* Program step semantics:

    program P with first instruction at PC index 1 transforms 
    state x into state y in one step, using instruction a PC index (fst x) *)

Definition mm2_step P x y := exists ρ, mm2_instr_at ρ (fst x) P /\ ρ // x ⇢ y.
#[local] Notation "P // x → y" := (mm2_step P x y).

(* Halting condition: program P cannot progress from s *)
Definition mm2_stop P s := forall s', not (P // s → s').

(* reflexive and transitive closure of program step semantics *)
#[local] Notation "P // x ↠ y" := (clos_refl_trans _ (mm2_step P) x y).

Definition mm2_terminates P s := exists s', P // s ↠ s' /\ mm2_stop P s'.
#[local] Notation "P // s ↓" := (mm2_terminates P s).

Definition MM2_PROBLEM := (list mm2_instr * nat * nat)%type.

(* Two-counter Machine Halting *)
Definition MM2_HALTING (P : MM2_PROBLEM) := 
  match P with (P,a,b) => P // (1,(a,b)) ↓ end.

(* Two-counter Machine Halting starting from (0, 0) *)
Definition MM2_ZERO_HALTING : list mm2_instr -> Prop := 
  fun P => P // (1,(0,0)) ↓.

(* Two-counter Machine Halting ending in (0, 0) *)
Definition MM2_HALTS_ON_ZERO (P : MM2_PROBLEM) := 
  match P with (P,a,b) => P // (1,(a,b)) ↠ (0,(0,0)) end.

(* injectivity of the step relation *)
Definition mm2_reversible (P : list mm2_instr) : Prop := 
  forall x y z, mm2_step P x z -> mm2_step P y z -> x = y.

(* k bounds the number of reachable configurations from x *)
Definition mm2_bounded (P : list mm2_instr) (k: nat) (x: mm2_state) : Prop := 
  exists (L: list mm2_state), (length L <= k) /\
    (forall (y: mm2_state), P // x ↠ y -> In y L).

(* uniform bound for number of reachable configurations *)
Definition mm2_uniformly_bounded (P : list mm2_instr) : Prop :=
  exists k, forall x, mm2_bounded P k x.

(* configuration trace P // x → x1 → x2 → ... → xn *)
Fixpoint mm2_trace (P : list mm2_instr) (x : mm2_state) (xs : list mm2_state) : Prop :=
  match xs with
  | nil => True
  | y::ys => P // x → y /\ mm2_trace P y ys
  end.

(* k bounds the number of steps in any run from x *)
Definition mm2_mortal (P : list mm2_instr) (k: nat) (x: mm2_state) : Prop :=
  forall (L: list mm2_state), mm2_trace P x L -> length L <= k.

(* uniform bound for number of steps until termination *)
Definition mm2_uniformly_mortal (P : list mm2_instr) : Prop :=
  exists k, forall x, mm2_mortal P k x.

(* Two-counter Machine Reversibility:
   Given a two-counter machine P,
   is the step function of P injective? *)
Definition MM2_REV : list mm2_instr -> Prop :=
  fun P => mm2_reversible P.

(* Reversible Two-counter Machine Halting:
   Given a reversible two-counter machine P and a configucation x,
   does a run in M starting from x eventually halt? *)
Definition MM2_REV_HALT : { P: list mm2_instr | mm2_reversible P } * mm2_state -> Prop :=
  fun '((exist _ P _), x) => P // x ↓.

(* Two-counter Machine Uniform Boundedness:
   Given a two-counter machine P,
   is there a uniform bound n,
   such that for any configuration x,
   the number of reacheable configurations from x in P is bounded by n? *)
Definition MM2_UBOUNDED : list mm2_instr -> Prop :=
  fun P => mm2_uniformly_bounded P.

(* Two-counter Machine Uniform Mortality:
   Given a two-counter machine P,
   is there a uniform bound n,
   such that for any configuration x,
   a run in P starting from x halts after at most n steps? *)
Definition MM2_UMORTAL : list mm2_instr -> Prop :=
  fun P => mm2_uniformly_mortal P.

Module MM2Notations.
  Notation mm2_state := (nat*(nat*nat))%type.
  Notation index x := (@fst nat (nat*nat) x).
  Notation value1 x := (fst (@snd nat (nat*nat) x)).
  Notation value2 x := (snd (@snd nat (nat*nat) x)).
  Notation "ρ // x ⇢ y" := (mm2_atom ρ x y).
  Notation "P // x → y" := (mm2_step P x y).
  Notation "P // x ↠ y" := (clos_refl_trans _ (mm2_step P) x y).
  Notation "P // s ↓" := (mm2_terminates P s).
End MM2Notations.
