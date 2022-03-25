(** This file is a proof of an equivalence relation on [com] that
    is not congruent. 
    
    In this file, [cequiv] represents an equivalence relation on [com].
    At the end of the file, [no_CSeq_congruence] shows that [cequiv]
    is not congruent. 
    
    See the [README.md] file for an overview of this problem. *)

From Coq Require Import Strings.String.
From EquivalenceNotCongruence Require Export Imp.

(** * [var_equiv_with_swap] *)

(** [xOrYOrOther] is a simple inductive type used in [var_equiv_with_swap] and
    [var_equiv_with_swap_sym] to make the proofs easier.  It is used along with
    [make_x_or_y_or_other] to determine whether a string is ["X"], ["Y"], or
    something else. *)

Inductive xOrYOrOther : string -> Type :=
  | IsX : xOrYOrOther "X"
  | IsY : xOrYOrOther "Y"
  | IsOther : forall s, xOrYOrOther s
  .
  
Definition make_x_or_y_or_other (x : string): xOrYOrOther x :=
  match x as m return xOrYOrOther m with
  | "X"%string => IsX
  | "Y"%string => IsY
  | n => IsOther n
  end. 

(** Our equivalence relation [cequiv] determines if two [com] are equal,
    where one [com] potentially has all uses of the ["X"] variable replaced
    by ["Y"], and vice-versa.
    
    [var_equiv_with_swap] is at the heart of this.  It is a [Prop] that holds
    in the following cases:
    
    - First argument is ["X"] and second argument is ["Y"]
    - First argument is ["Y"] and second argument is ["X"]
    - Both arguements are neither ["X"] nor ["Y"] *)

Definition var_equiv_with_swap (s1 s2 : string) : Prop :=
  match make_x_or_y_or_other s1 with
  | IsX =>
      match make_x_or_y_or_other s2 with
      | IsY => True
      | _ => False
      end
  | IsY =>
      match make_x_or_y_or_other s2 with
      | IsX => True
      | _ => False
      end
  | IsOther s1' =>
      match make_x_or_y_or_other s2 with
      | IsOther s2' => s1' = s2'
      | _ => False
      end
  end.
  
(** Examples of [var_equiv_with_swap]. *)
  
Example var_equiv_example1 : var_equiv_with_swap "X" "Y".
Proof. reflexivity. Qed.
Example var_equiv_example2 : var_equiv_with_swap "Y" "X".
Proof. reflexivity. Qed.
Example var_equiv_example3 : var_equiv_with_swap "G" "G".
Proof. reflexivity. Qed.
Example var_equiv_example4 : var_equiv_with_swap "X" "X" -> False.
Proof. unfold var_equiv_with_swap. simpl. intros. auto. Qed.
Example var_equiv_example5 : var_equiv_with_swap "G" "Y" -> False.
Proof. intros. unfold var_equiv_with_swap in *. simpl in *. auto. Qed.
Example var_equiv_example6 : var_equiv_with_swap "Y" "G" -> False.
Proof. intros. unfold var_equiv_with_swap in *. simpl in *. auto. Qed.

(** Proving symmetry and transitivity for [var_equiv_with_swap]. *)

Theorem var_equiv_with_swap_sym :
  forall s1 s2, var_equiv_with_swap s1 s2 -> var_equiv_with_swap s2 s1.
Proof.
  unfold var_equiv_with_swap. intros s1 s2 H.
  destruct (make_x_or_y_or_other s1) eqn:E;
  destruct (make_x_or_y_or_other s2) eqn:F;
  try destruct H;
  reflexivity.
Qed.

Theorem var_equiv_with_swap_trans_is_same :
  forall s1 s2 s3, var_equiv_with_swap s1 s2 -> var_equiv_with_swap s2 s3 -> s1 = s3.
Proof.
  unfold var_equiv_with_swap. intros s1 s2 s3 H12 H23.
  destruct (make_x_or_y_or_other s1) eqn:E;
  destruct (make_x_or_y_or_other s2) eqn:F;
  destruct (make_x_or_y_or_other s3) eqn:G;
  simpl; auto; try destruct H12; try destruct H23. auto.
  Qed.

(** * [aequiv_with_swap]

    This is similar to [var_equiv_with_swap], but lifted to [aexp]. 
    Examples follow, as well as proofs of symmetry and transitivity. *)

Fixpoint aequiv_with_swap (a1 a2 : aexp) : Prop :=
  match (a1,a2) with
  | (ANum n1, ANum n2) => n1 = n2
  | (AId s1, AId s2) => var_equiv_with_swap s1 s2
  | (<{a1' + a1''}>, <{a2' + a2''}>) => aequiv_with_swap a1' a2' /\ aequiv_with_swap a1'' a2''
  | (<{a1' - a1''}>, <{a2' - a2''}>) => aequiv_with_swap a1' a2' /\ aequiv_with_swap a1'' a2''
  | (<{a1' * a1''}>, <{a2' * a2''}>) => aequiv_with_swap a1' a2' /\ aequiv_with_swap a1'' a2''
  | _ => False
  end.

Example aequiv_with_swap_example1 : aequiv_with_swap X Y.
Proof. reflexivity. Qed.
Example aequiv_with_swap_example2 :
  aequiv_with_swap <{ X + 100 - Y * (AId "G"%string) }> <{ Y + 100 - X * (AId "G"%string) }>.
Proof. now auto. Qed.
Example aequiv_with_swap_example3 : ~ (aequiv_with_swap <{ X }> <{ X }>).
Proof. simpl. intro H. apply var_equiv_example4. auto. Qed.
Example aequiv_with_swap_example4 :
  ~ (aequiv_with_swap <{ X + 100 - Y - (AId "G"%string) }> <{ Y + 100 - X * (AId "G"%string) }>).
Proof. simpl. intro H. destruct H. destruct H. Qed.

Theorem aequiv_with_swap_sym : forall a1 a2, aequiv_with_swap a1 a2 -> aequiv_with_swap a2 a1.
Proof.
  induction a1; destruct a2; simpl; intro H; try destruct H.
  - auto.
  - now apply var_equiv_with_swap_sym.
  - split. apply IHa1_1. assumption. apply IHa1_2. assumption.
  - split. apply IHa1_1. assumption. apply IHa1_2. assumption.
  - split. apply IHa1_1. assumption. apply IHa1_2. assumption.
  Qed.
  
Theorem aequiv_with_swap_trans_is_same :
  forall a1 a2 a3, aequiv_with_swap a1 a2 -> aequiv_with_swap a2 a3 -> a1 = a3.
Proof.
  unfold aequiv_with_swap. induction a1; destruct a2; destruct a3; simpl; subst;
  intros H12 H23; auto; try destruct H12; try destruct H23; auto.
  - set (G := var_equiv_with_swap_trans_is_same _ _ _ H12 H23). rewrite G. auto.
  - fold aequiv_with_swap in *.
    specialize (IHa1_1 _ _ H H1).
    specialize (IHa1_2 _ _ H0 H2).
    now subst.
  - fold aequiv_with_swap in *.
    specialize (IHa1_1 _ _ H H1).
    specialize (IHa1_2 _ _ H0 H2).
    now subst.
  - fold aequiv_with_swap in *.
    specialize (IHa1_1 _ _ H H1).
    specialize (IHa1_2 _ _ H0 H2).
    now subst.
  Qed.

(** * [bequiv_with_swap]

    Similar to [aequiv_with_swap], but for [bexp]. *)

Fixpoint bequiv_with_swap (b1 b2 : bexp) : Prop :=
  match (b1,b2) with
  | (<{ true }>, <{ true }>) => True
  | (<{ false }>, <{ false }>) => True
  | (<{ a1 = a1' }>, <{ a2 = a2' }>) => aequiv_with_swap a1 a2 /\ aequiv_with_swap a1' a2'
  | (<{ a1 <= a1' }>, <{ a2 <= a2' }>) => aequiv_with_swap a1 a2 /\ aequiv_with_swap a1' a2'
  | (<{ ~ b }>, <{ ~ b' }>) => bequiv_with_swap b b'
  | (<{ b1' && b1'' }>, <{ b2' && b2'' }>) => bequiv_with_swap b1' b2' /\ bequiv_with_swap b1'' b2''
  | _ => False
  end.

Theorem bequiv_with_swap_sym : forall b1 b2, bequiv_with_swap b1 b2 -> bequiv_with_swap b2 b1.
Proof.
  induction b1; destruct b2; simpl; intro H; try destruct H; try auto.
  - split; apply aequiv_with_swap_sym; assumption.
  - split; apply aequiv_with_swap_sym; assumption.
  Qed.

Theorem bequiv_with_swap_trans_is_same :
  forall b1 b2 b3, bequiv_with_swap b1 b2 -> bequiv_with_swap b2 b3 -> b1 = b3.
Proof.
  unfold bequiv_with_swap. induction b1; destruct b2; destruct b3; simpl; subst;
  intros H12 H23; auto; try destruct H12; try destruct H23; auto.
  - replace a4 with a1 by (apply aequiv_with_swap_trans_is_same with a0; assumption).
    replace a5 with a2 by (apply aequiv_with_swap_trans_is_same with a3; assumption).
    reflexivity.
  - replace a4 with a1 by (apply aequiv_with_swap_trans_is_same with a0; assumption).
    replace a5 with a2 by (apply aequiv_with_swap_trans_is_same with a3; assumption).
    reflexivity.
  - fold bequiv_with_swap in *.
    replace b3 with b1. reflexivity.
    apply IHb1 with b2; assumption.
  - fold bequiv_with_swap in *.
    specialize (IHb1_1 _ _ H H1).
    specialize (IHb1_2 _ _ H0 H2).
    now subst.
  Qed.

(** * [cequiv_with_swap]

    Similar to [aequiv_with_swap], but for [com]. *)

Fixpoint cequiv_with_swap (c1 c2 : com) : Prop :=
  match (c1, c2) with
  | (<{ skip }>, <{ skip }>) => True
  | (<{ s1 := a1 }>, <{ s2 := a2 }>) => var_equiv_with_swap s1 s2 /\ aequiv_with_swap a1 a2
  | (<{ c1'; c1'' }>, <{ c2' ; c2'' }>) => cequiv_with_swap c1' c2' /\ cequiv_with_swap c1'' c2''
  | (<{ if b1 then c1' else c1'' end }>, <{ if b2 then c2' else c2'' end }>) => 
      bequiv_with_swap b1 b2 /\ cequiv_with_swap c1' c2' /\ cequiv_with_swap c1'' c2''
  | _ => False
  end.

Example cequiv_with_swap_example1 :
  cequiv_with_swap
    <{ skip ; X := Y + 100 ; "G" := X }>
    <{ skip ; Y := X + 100 ; "G" := Y }>.
Proof. now auto. Qed.
Example cequiv_with_swap_example2 :
  ~ (cequiv_with_swap <{ skip ; "G" := Y + 100 }> <{ skip ; "F" := X + 100 }>).
Proof. simpl. intro H. destruct H.  destruct H0. discriminate. Qed.
  
Theorem cequiv_with_swap_sym : forall c1 c2, cequiv_with_swap c1 c2 -> cequiv_with_swap c2 c1.
Proof.
  induction c1; destruct c2; simpl; intro H; try destruct H; try auto.
  - split. apply var_equiv_with_swap_sym. assumption. apply aequiv_with_swap_sym; assumption.
  - split.
    + apply bequiv_with_swap_sym. assumption.
    + destruct H0. apply IHc1_1 in H0. apply IHc1_2 in H1. split; assumption.
  Qed.

Theorem cequiv_with_swap_trans_is_same :
  forall c1 c2 c3, cequiv_with_swap c1 c2 -> cequiv_with_swap c2 c3 -> c1 = c3.
Proof.
  unfold cequiv_with_swap. induction c1; destruct c2; destruct c3; simpl; subst;
  intros H12 H23; auto; try destruct H12; try destruct H23; auto.
  - replace x1 with x. replace a1 with a. reflexivity.
    apply aequiv_with_swap_trans_is_same with a0; assumption.
    apply var_equiv_with_swap_trans_is_same with x0; assumption.
  - fold cequiv_with_swap in *.
    specialize (IHc1_1 _ _ H H1).
    specialize (IHc1_2 _ _ H0 H2).
    now subst.
  - fold cequiv_with_swap in *.
    destruct H0,H2.
    specialize (IHc1_1 _ _ H0 H2).
    specialize (IHc1_2 _ _ H3 H4).
    subst.
    replace b1 with b; try reflexivity.
    apply bequiv_with_swap_trans_is_same with b0; assumption.
  Qed.

(** * Equivalence Relation on [com]: [cequiv]

    [cequiv] is the equivalence relation between two [com]s.

    It says that:
    
    - in the case of [CEquivRefl], two [com] are equal
    - in the case of [CEquivSwap], two [com] are related under [cequiv_with_swap]
      (where all ["X"] and ["Y"] have been swapped in the second [com]). *)

Inductive cequiv : com -> com -> Prop :=
  | CEquivRefl : forall c, cequiv c c
  | CEquivSwap : forall c1 c2, cequiv_with_swap c1 c2 -> cequiv c1 c2
  .
  
Example cequiv_example1 :
  cequiv
    <{ skip ; X := Y + 100 ; "G" := X }>
    <{ skip ; Y := X + 100 ; "G" := Y }>.
Proof. constructor. simpl. unfold var_equiv_with_swap. simpl. auto. Qed.
Example cequiv_example2:
  cequiv
    <{ skip ; X := X + 100 ; "G" := X }>
    <{ skip ; X := X + 100 ; "G" := X }>.
Proof. constructor. Qed.
Example cequiv_example3:
  ~ (cequiv <{ X := X + 100 ; "G" := Y }> <{ X := X + 100 ; "G" := X }>).
Proof.
  simpl. intros H. inversion H; subst.
  simpl in H0. destruct H0. destruct H0. unfold var_equiv_with_swap in H0. simpl in H0. destruct H0.
Qed.

(** Proof of reflexivity, symmetry, and transitivity for [cequiv]. *)

Lemma refl_cequiv : forall (c : com), cequiv c c.
Proof. constructor. Qed.

Lemma sym_cequiv : forall (c1 c2 : com), cequiv c1 c2 -> cequiv c2 c1.
Proof. intros c1 c2 H. inversion H; subst. assumption. apply cequiv_with_swap_sym in H0. constructor. auto.  Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com), cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof.
  intros c1 c2 c3 H12 H23.
  inversion H12; subst; inversion H23; subst; try auto.
  - replace c3 with c1. constructor.
    apply cequiv_with_swap_trans_is_same with c2; assumption. 
  Qed.

(** * Proof of no congruence

    This is the proof that this file has been working to.  This says that
    given that the [com] [c1] and [c1'] are equivalent, and [c2] and [c2']
    are equivalent, we can't prove that [c1; c2] is equivalent to 
    [c1'; c2'].  This means that [cequiv] is not congruent. 
    
    This proof uses the example that [X := 0] is equivalent with
    [X := 0] trivially, and [X := X + 1] is equivalent with
    [Y := Y + 1] by replacing [X] with [Y].  But
    [X := 0; X := X + 1] is not equivalent with [X := 0; Y := Y + 1]. *)
 
Theorem no_CSeq_congruence : 
  ~ (forall c1 c1' c2 c2',
      cequiv c1 c1' -> cequiv c2 c2' -> cequiv <{ c1;c2 }> <{ c1';c2' }>).
Proof.
  unfold not. intros H.
  assert (cequiv <{ X := 100 }> <{ X := 100 }>) by constructor.
  assert (cequiv <{ X := X + 1 }> <{ Y := Y + 1 }>).
  { constructor.  simpl. unfold var_equiv_with_swap. simpl. auto. }
  specialize (H _ _ _ _ H0 H1). clear H0 H1. inversion H; subst.
  unfold cequiv_with_swap in H0. destruct H0. destruct H0. unfold var_equiv_with_swap in H0. simpl in H0. destruct H0.
  Qed.  
