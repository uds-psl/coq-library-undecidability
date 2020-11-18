From Coq Require List Vector.

From Undecidability.L Require Import L Datatypes.Lists.
From Undecidability.TM Require Import TM Util.TM_facts.

Import ListNotations Vector.VectorNotations.

Definition encListTM {Σ : Type} (s b : Σ) (l : list bool) :=
  (map (fun (x : bool) => (if x then s else b)) l).

Definition encTM {Σ : Type} (s b : Σ) (l : list bool) :=
  @midtape Σ [] b (encListTM s b l).

  
Definition TM_computable {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) := 
  exists n : nat, exists Σ : finType, exists s b : Σ, s <> b /\ 
  exists M : TM Σ (k + 1 + n),
  forall v : Vector.t (list bool) k, 
  (forall m, R v m <-> exists q t, TM.eval M (start M) ((Vector.map (encTM s b) v ++ [niltape]) ++ Vector.const niltape n) q t
                                /\ nth_error (Vector.to_list t) k = Some (encTM s b m)) /\
  (forall q t, TM.eval M (start M) ((Vector.map (encTM s b) v ++ [niltape]) ++ Vector.const niltape n) q t ->
          exists m, nth_error (Vector.to_list t) k = Some (encTM s b m)).

Definition TM₁_computable {k} (Σ : finType) (R : Vector.t (list bool) k -> (list bool) -> Prop) := 
  exists s1 s2 b : Σ, s1 <> s2 /\ s1 <> b /\ s2 <> b /\
  exists M : TM Σ 1,
  forall v : Vector.t (list bool) k, 
  (forall m, R v m <-> exists q, TM.eval M (start M) [midtape [] b (Vector.fold_right (fun l s => encListTM s1 s2 l ++ s)%list v List.nil)] q [encTM s1 s2 m]) /\
  (forall q t, TM.eval M (start M) [midtape [] b (Vector.fold_right (fun l s => encListTM s1 s2 l ++ s)%list v List.nil)] q t ->
          exists m, t = [encTM s1 s2 m]).
      
Definition encL (l : list bool) := list_enc l.

Definition L_computable {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) := 
  exists s, forall v : Vector.t (list bool) k, 
      (forall m, R v m <-> L.eval (Vector.fold_left (fun s n => L.app s (encL n)) s v) (encL m)) /\
      (forall o, L.eval (Vector.fold_left (fun s n => L.app s (encL n)) s v) o -> exists m, o = encL m).
