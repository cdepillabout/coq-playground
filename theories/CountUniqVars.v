
(** This file is a proof of an equivalence relation on [com] that is not 
    congruent.
    
    In this file, [cequiv] represents an equivalence relation on [com].
    At the end of the file, [no_CSeq_congruence] shows that [cequiv]
    is not congruent.
    
    See the [README.md] file for an overview of this approach. *)

From Coq Require Import Lists.List. 
From Coq Require Import Lists.ListSet.
From Coq Require Import Strings.String.
From EquivalenceNotCongruence Require Export Imp.

Import Coq.Lists.List.ListNotations.

Section set_helpers.

  Variable A : Type.
  Hypothesis Aeq_dec : forall x y:A, {x = y} + {x <> y}.

  Definition set_eq (x y : set A) := set_diff Aeq_dec x y = empty_set A /\ set_diff Aeq_dec y x = empty_set A.

End set_helpers.

Fixpoint uniq_var_asgn (c : com): set string :=
  match c with
  | <{ skip }> => empty_set string
  | <{ x := _ }> => [ x ]
  | <{ c1 ; c2 }> => set_union string_dec (uniq_var_asgn c1) (uniq_var_asgn c2)
  | <{ if _ then c1 else c2 end }> => set_union string_dec (uniq_var_asgn c1) (uniq_var_asgn c2)
  end.
  
Example uniq_vars_asgn_example1 : set_eq _ string_dec (uniq_var_asgn <{ X := 3 }>) [X].
Proof. simpl. unfold set_eq. auto. Qed.

Example uniq_vars_asgn_example2 : set_eq _ string_dec (uniq_var_asgn <{ X := 3; X := 4 }>) [X].
Proof. simpl. unfold set_eq. auto. Qed.

Example uniq_vars_asgn_example3 : set_eq _ string_dec (uniq_var_asgn <{ Y := 3; X := 4 }>) [X; Y].
Proof. simpl. unfold set_eq. auto. Qed.

Example uniq_vars_asgn_example4 : set_eq _ string_dec (uniq_var_asgn <{ Y := 3; X := 4; Y := 100 }>) [X; Y].
Proof. simpl. unfold set_eq. auto. Qed.

Definition count_uniq_var_asgn (c : com): nat := List.length (uniq_var_asgn c).

Example count_uniq_var_asgn_example1 : count_uniq_var_asgn <{ X := 100 }> = 1.
Proof. reflexivity. Qed.

Example count_uniq_var_asgn_example2 : count_uniq_var_asgn <{ skip }> = 0.
Proof. reflexivity. Qed.

Example count_uniq_var_asgn_example3 : count_uniq_var_asgn <{ X := 100 ; Y := 200 }> = 2.
Proof. reflexivity. Qed.

Example count_uniq_var_asgn_example4 : count_uniq_var_asgn <{ X := 100 ; X := 200 }> = 1.
Proof. reflexivity. Qed.

Definition cequiv (c1 c2 : com) : Prop := count_uniq_var_asgn c1 = count_uniq_var_asgn c2.

Example cequiv_example1 : cequiv <{ X := 100 }> <{ X := 200 }>.
Proof. reflexivity. Qed.

Example cequiv_example2 : cequiv <{ X := 100 }> <{ X := 200; skip }>.
Proof. reflexivity. Qed.

Example cequiv_example3 : cequiv <{ X := 0; X := 100; Y := 3 }> <{ X := 200; skip; Y := X }>.
Proof. reflexivity. Qed.

Lemma refl_cequiv : forall (c : com), cequiv c c.
Proof. unfold cequiv. try reflexivity. Qed.

Lemma sym_cequiv : forall (c1 c2 : com), cequiv c1 c2 -> cequiv c2 c1.
Proof. unfold cequiv. intros. now symmetry. Qed.

Lemma trans_cequiv : forall (c1 c2 c3 : com), cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Proof. unfold cequiv. intros. now rewrite H. Qed.

Theorem no_CSeq_congruence : 
  ~ (forall c1 c1' c2 c2',
      cequiv c1 c1' -> cequiv c2 c2' -> cequiv <{ c1;c2 }> <{ c1';c2' }>).
Proof.
  unfold not. unfold cequiv. intros H.
  assert (cequiv <{ X := 100 }> <{ X := 100 }>) by reflexivity.
  assert (cequiv <{ X := 200 }> <{ Y := 200 }>) by reflexivity.
  specialize (H _ _ _ _ H0 H1).
  unfold count_uniq_var_asgn in H. simpl in H. discriminate.
  Qed.