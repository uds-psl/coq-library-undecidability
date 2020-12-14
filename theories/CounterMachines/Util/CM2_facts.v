Require Import List Lia.
Import ListNotations.

Require Import Undecidability.CounterMachines.CM2.
Require Import Undecidability.CounterMachines.Util.Nat_facts.

Require Import ssreflect.

Set Default Goal Selector "!".

Lemma haltingP {cm c} : halting cm c <-> length cm <= state c.
Proof.
  move:c => [p a b]. rewrite /halting /=.
  move Hoi: (nth_error cm p) => oi.
  case: oi Hoi; last by move=> /nth_error_None.
  move=> [] x => [|?] Hp /=.
  - constructor; [by case; lia | by rewrite -nth_error_None Hp].
  - move: x a b Hp => [] [|?] [|?]; 
      (constructor; [by case; lia | by rewrite -nth_error_None Hp]).
Qed.

Lemma halting_eq {cm c n} : halting cm c -> Nat.iter n (step cm) c = c.
Proof.
  move=> Hc. elim: n; first done.
  move=> ? /= ->. by rewrite Hc.
Qed.

(* halting is monotone *)
Lemma halting_monotone {cm x} (n m: nat) : n <= m ->
  halting cm (Nat.iter n (step cm) x) -> halting cm (Nat.iter m (step cm) x).
Proof.
  move=> ? ?. have -> : m = n + (m-n) by lia.
  rewrite iter_plus. elim: (m-n); [done | by move=> * /=; congruence].
Qed.

Lemma values_ub cm c n : 
  value1 (Nat.iter n (CM2.step cm) c) + value2 (Nat.iter n (CM2.step cm) c) <= n + value1 c + value2 c.
Proof.
  move Hk : (n + value1 c + value2 c) => k.
  have : n + value1 c + value2 c <= k by lia.
  elim: n k c {Hk}; first done.
  move=> n IH k [p a b]. rewrite -/(1 + n) iter_plus /=. 
  case: (nth_error cm p).
  - move=> [] [] => [||?|?]; move: a b => [|?] [|?] /= ?; apply: IH => /=; by lia.
  - move=> ?. apply: IH => /=. by lia.
Qed.
