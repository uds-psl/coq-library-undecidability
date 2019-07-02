From Undecidability.L Require Import L.
From Undecidability.L Require Import AbstractMachines.LargestVar.

(** ** Abstract Heap Machine *)
Section Lin.

  Let HA:=nat.

  Notation clos := (term * HA)%type.
  Inductive task := appT | closT (g:clos).

  Inductive heapEntry := heapEntryC (g:clos) (alpha:HA).

  (** *** Heaps *)
  
  Let Heap := list heapEntry.
  Implicit Type H : Heap.
  Definition put H e := (H++[e],|H|).
  Definition get H alpha:= nth_error H alpha.
  Definition extended H H' := forall alpha m, get H alpha = Some m -> get H' alpha = Some m.

  
  Fixpoint lookup H alpha x : option clos:=
    match get H alpha with
      Some (heapEntryC bound env') =>
      match x with
        0 => Some bound
      | S x' => lookup H env' x'
      end
    |  _ => None
    end.

  (** *** Reduction Rules *)

  Definition state := (list task * list clos *Heap)%type.

  Hint Transparent state.

  Inductive step : state -> state -> Prop :=
    step_pushVal a s T V H:
      step (closT (lam s,a)::T,V,H) (T,(s,a)::V,H)
  | step_beta b s g H H' c T V:
      put H (heapEntryC g b) = (H',c)
      -> step (appT::T,g::(s,b)::V,H) (closT (s,c) ::T,V,H')
  | step_load a x g T V H:
      lookup H a x = Some g
      -> step (closT (var x,a)::T,V,H) (T,g::V,H)
  | step_app s t a T V H: step (closT (app s t,a)::T,V,H) (closT (s,a)::closT(t,a)::appT::T,V,H).

  Hint Constructors step.

  
  (** *** Unfolding *)

  Inductive unfolds H a: nat -> term -> term -> Prop :=
  | unfoldsUnbound k n :
      n < k ->
      unfolds H a k (var n) (var n)
  | unfoldsBound k b s s' n:
      n >= k ->
      lookup H a (n-k) = Some (s,b) ->
      unfolds H b 1 s s' ->
      unfolds H a k (var n) (lam s')
  | unfoldsLam k s s':
      unfolds H a (S k) s s' ->
      unfolds H a k (lam s) (lam s')
  | unfoldsApp k (s t s' t' : term):
      unfolds H a k s s' ->
      unfolds H a k t t' ->
      unfolds H a k (s t) (s' t').

  
  Inductive reprC : Heap -> clos -> term -> Prop :=
    reprCC H s a s' :
      unfolds H a 1 s s' ->
      reprC H (s,a) (lam s').

  Definition init s :state := ([closT (s,0)],[],[]).

End Lin.

Module clos_notation.
  Notation clos := (term * nat)%type.
End clos_notation.
Import clos_notation.
Hint Transparent state.

Definition largestVarC : clos -> nat := (fun '(s,_) => largestVar s).

Definition largestVarCs (T:list clos) :=
  maxl (map largestVarC T).

Definition largestVarH (H:list heapEntry) :=
  maxl (map (fun e:heapEntry => let (q,_) := e in largestVarC q) H).


Definition sizeC g :=
  match g with
    (s,a) => size s + a 
  end.

Definition sizeT t :=
  match t with
    appT => 1
  | closT g => sizeC g
  end.

Definition sizeHE e :=
  match e with
    heapEntryC g b => sizeC g + b
  end.
Definition sizeH H :=
  sumn (map sizeHE H).

Definition sizeSt '(T,V,H) := sumn (map sizeC T) + sumn (map sizeC V) + sizeH H.
