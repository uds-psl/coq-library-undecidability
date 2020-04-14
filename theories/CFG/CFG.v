Require Import List.
Import ListNotations.

Definition stack (X : Type) := list (list X * list X).

(** ** Post Grammars *)

Notation sig := nat.
(** a rule maps a non-terminal symbol to a word *)
Definition rule : Type := sig * list sig.
(** a context-free grammar consist of a start symbol and a list of rules *)
Definition cfg : Type := sig * list rule.
Definition rules (G : cfg) := snd G.
Definition startsym (G : cfg) := fst G.

(** single step context-free derivation *)
Inductive rew_cfg : cfg -> list sig -> list sig -> Prop :=
  | rewR R x a y v : In (a, v) (rules R) -> rew_cfg R (x++[a]++y) (x++v++y).
Hint Constructors rew_cfg : core.

(** reflexive, transitive closure of single step context-free derivation *)
Inductive rewt (S: cfg) (x: list sig) : list sig -> Prop :=
  | rewtRefl : rewt S x x
  | rewtRule y z : rewt S x y -> rew_cfg S y z -> rewt S x z.
Hint Constructors rewt : core.

(** a word is terminal if it contains no non-terminals *)
Definition terminal G x := ~ exists y, rew_cfg G x y.

(** the language of a grammar consists of all derivable terminal words *)
Definition L (G : cfg) x := rewt G [startsym G] x /\ terminal G x.

(** The Context-free Palindrome Problem is
  given a context-free grammar to determine whether
  its language contains a palindrome. *)
Definition CFP : cfg -> Prop :=
  fun G => exists x, L G x /\ x = List.rev x.

(** The Context-free Intersection Problem is
  given two context-free grammars to determine whether 
  their intersection is not empty. *)
Definition CFI : cfg * cfg -> Prop :=
  fun '(G1, G2) => exists x, L G1 x /\ L G2 x.
