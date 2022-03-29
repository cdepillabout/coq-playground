From Coq Require Import Lists.List.

Import ListNotations.

Inductive non_empty_list (A : Type): Type :=
  | NonEmptyListSingle : forall (a : A), non_empty_list A
  | NonEmptyList : forall (a : A) (l : non_empty_list A), non_empty_list A.

Arguments NonEmptyListSingle {A} a.  
Arguments NonEmptyList {A} a l.

Fixpoint non_empty_list_to_list {A} (nel : non_empty_list A) : list A :=
  match nel with
  | NonEmptyListSingle a => [a]
  | NonEmptyList a l => a :: non_empty_list_to_list l
  end.

Fixpoint list_to_non_empty_list {A} (a : A) (l : list A) : non_empty_list A :=
  match l with
  | [] => NonEmptyListSingle a
  | h :: t => NonEmptyList a (list_to_non_empty_list h t)
  end.