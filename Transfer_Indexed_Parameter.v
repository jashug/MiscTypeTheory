Set Universe Polymorphism.

(*
We show how to prove the induction principle of parametrized lists
from the induction principle for indexed lists.
*)

Inductive list_param@{i j | i <= j} (T : Type@{i}) : Type@{j} :=
  | nilp : list_param T
  | consp : T -> list_param T -> list_param T.
Check list_param_rect.
(*
list_param_rect
     : forall (T : Type) (P : list_param T -> Type),
       P (nilp T) ->
       (forall (t : T) (l : list_param T), P l -> P (consp T t l)) ->
       forall l : list_param T, P l
*)

Inductive list_index@{i j | i < j} : Type@{i} -> Type@{j} :=
  | nili : forall (A : Type@{i}), list_index A
  | consi : forall (A : Type@{i}), A -> list_index A -> list_index A
  .
Check list_index_rect.
(*
list_index_rect
     : forall P : forall T : Type, list_index T -> Type,
       (forall A : Type, P A (nili A)) ->
       (forall (A : Type) (a : A) (l : list_index A), P A l -> P A (consi A a l)) ->
       forall (T : Type) (l : list_index T), P T l
*)

Definition list_param_rect_from_index_rect (T : Type) (P : list_index T -> Type)
  (step_nil : P (nili T))
  (step_cons : forall (t : T) (l : list_index T), P l -> P (consi T t l))
  (l : list_index T)
  : P l
  := let P' T' (l : list_index T') : Type
      := forall e : T = T',
         (eq_rect T (fun T => list_index T -> Type) P T' e) l
     in
     list_index_rect P'
     (* nil case *)
     (fun A e =>
      match e in _ = A
      return
        (eq_rect T (fun T => list_index T -> Type) P A e) (nili A)
      with eq_refl => step_nil
      end)
     (* cons case *)
     (fun A a l IH e =>
      match e in _ = A
      return
        forall a l, P' A l ->
        (eq_rect T (fun T => list_index T -> Type) P A e) (consi A a l)
      with eq_refl => fun a l IH => step_cons a l (IH eq_refl)
      end a l IH)
     T
     l
     eq_refl.
