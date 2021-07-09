From Coq Require List Vector.

From Undecidability.L Require Import L Datatypes.Lists Datatypes.LNat.
From Undecidability Require Export Util.L_computable.
From Undecidability.TM Require Import TM Util.TM_facts.
From Undecidability Require Export TM_computable.

Import ListNotations Vector.VectorNotations.

Definition encBoolsListTM {Σ : Type} (s b : Σ) (l : list bool) :=
  (map (fun (x : bool) => (if x then s else b)) l).

Definition encBoolsTM {Σ : Type} (s b : Σ) (l : list bool) :=
  @midtape Σ [] b (encBoolsListTM s b l).

Definition TM_bool_computable {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) := 
  exists n : nat, exists Σ : finType, exists s b : Σ, s <> b /\ 
  exists M : TM Σ (1 + k + n),
  forall v : Vector.t (list bool) k, 
  (forall m, R v m <-> exists q t, TM.eval M (start M) ((niltape :: Vector.map (encBoolsTM s b) v) ++ Vector.const niltape n) q t
                                /\ Vector.hd t = encBoolsTM s b m) /\
  (forall q t, TM.eval M (start M) ((niltape :: Vector.map (encBoolsTM s b) v) ++ Vector.const niltape n) q t ->
          exists m, Vector.hd t = encBoolsTM s b m).

Definition TM₁_bool_computable {k} (Σ : finType) (R : Vector.t (list bool) k -> (list bool) -> Prop) := 
  exists s1 s2 b : Σ, s1 <> s2 /\ s1 <> b /\ s2 <> b /\
  exists M : TM Σ 1,
  forall v : Vector.t (list bool) k, 
  (forall m, R v m <-> exists q, TM.eval M (start M) [midtape [] b (Vector.fold_right (fun l s => encBoolsListTM s1 s2 l ++ s)%list v List.nil)] q [encBoolsTM s1 s2 m]) /\
  (forall q t, TM.eval M (start M) [midtape [] b (Vector.fold_right (fun l s => encBoolsListTM s1 s2 l ++ s)%list v List.nil)] q t ->
          exists m, t = [encBoolsTM s1 s2 m]).
      
Definition encBoolsL (l : list bool) := list_enc l.

Definition L_bool_computable {k} (R : Vector.t (list bool) k -> (list bool) -> Prop) := 
  exists s, forall v : Vector.t (list bool) k, 
      (forall m, R v m <-> L.eval (Vector.fold_left (fun s n => L.app s (encBoolsL n)) s v) (encBoolsL m)) /\
      (forall o, L.eval (Vector.fold_left (fun s n => L.app s (encBoolsL n)) s v) o -> exists m, o = encBoolsL m).
