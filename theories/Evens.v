
From Coq Require Import Sorting.Sorted.
From Coq Require Import Lists.List.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import Lia.

Import ListNotations.



Fixpoint selectEvens (l : list nat): list nat :=
  match l with
  | [] => []
  | (h :: t) => 
    if even h
    then h :: selectEvens t
    else selectEvens t
  end.
  
Check selectEvens [1;2;3;4;100;101;300;299] = [2;4;100;300].

Inductive selectEvensInd : list nat -> list nat -> Prop :=
  | SelectEvensEmpty : selectEvensInd [] []
  | SelectEvensEven :
      forall x l selected,
      selectEvensInd l selected ->
      even x = true ->
      selectEvensInd (x :: l) (x :: selected)
  | SelectEvensOdd :
      forall x l selected,
      selectEvensInd l selected ->
      even x = false ->
      selectEvensInd (x :: l) selected
  .

Example selectEvensInd_example_1 : selectEvensInd [1;2;3;4;100;101;300;299] [2;4;100;300].
Proof. repeat constructor. Qed.
Example selectEvensInd_example_2 : selectEvensInd [1] [1] -> False.
Proof. intros H. inversion H; subst. discriminate. inversion H2. Qed.

  
Theorem selectEvensInd_preserves_in :
  forall l selected a, selectEvensInd l selected -> In a selected -> In a l.
Proof.
  intros l selected a Hsel. generalize dependent a.
  induction Hsel; subst.
  - auto.
  - intros a Hin. destruct Hin.
    + subst. now left.
    + specialize (IHHsel _ H0).
      now right.
  - intros a Hin. specialize (IHHsel _ Hin).
    now right.
  Qed.

Theorem selectEvensInd_same_as_selectEvens :
  forall l selected, selectEvensInd l selected -> selectEvens l = selected.
Proof.
  intros l selected H.
  induction H.
  - auto.
  - simpl.
    now rewrite H0,IHselectEvensInd.
  - simpl.
    now rewrite H0,IHselectEvensInd.
  Qed.

Theorem selectEvens_same_as_selectEvensInd :
  forall l selected, selectEvens l = selected -> selectEvensInd l selected.
Proof.
  (*
  intros l selected. generalize dependent l.
  induction selected.
  - destruct l.
    + intros. constructor.
    + simpl.
  *)
  induction l.
  - simpl. intros selected H. rewrite <- H. constructor.
  - simpl. intros selected H.
    destruct (even a) eqn:E.
    + destruct selected; try discriminate.
      inversion H; subst.
      constructor; try assumption.
      now apply IHl.
    + constructor; try assumption.
      now apply IHl.
  Qed.

Theorem selectEvensPreservesIn : forall l a, In a (selectEvens l) -> In a l.
Proof.
  (*
  intros l.
  remember (selectEvens l) as c.
  symmetry in Heqc.
  apply selectEvens_same_as_selectEvensInd in Heqc.
  intros a H. apply selectEvensInd_preserves_in with c; assumption. *)
  intros l a HInaselect.
  remember (selectEvens l) as c eqn:Heqc. symmetry in Heqc.
  (** Turn [selectEvens l = c] into [selectEvensInd l c]. *)
  apply selectEvens_same_as_selectEvensInd in Heqc.
  (** Induction over [selectEvensInd l c] *)
  induction Heqc.
  - (** Constructor [SelectEvensEmpty : selectEvensInd [] []].
        This is the case where [In a []], which we know can't happen. *)
    auto.
  - (** Constructor [SelectEvensEven : selectEvensInd l selected -> even x = true -> selectEvensInd (x :: l) (x :: selected)].
        This is the case where we know [In a (x :: selected)]. *)
     destruct HInaselect.
    + (** Here we know [x = a] and we need to prove [In a (x :: l)]. *)
      subst. now left.
    + (** Here we know [In a selected] and we need to prove [In a (x :: l)].
          We use the induction hypothesis: [In a selected -> In a l]. *)
      right. apply IHHeqc. assumption.
  - (** Constructor [SelectEvensOdd : selectEvensInd l selected -> even x = false -> selectEvensInd (x :: l) selected].
        Similar to the previous case. *)
    right. apply IHHeqc. assumption.
  Qed.
  
Theorem selectEvensPreservesIn2 : forall l a, In a (selectEvens l) -> In a l.
Proof.
  (*
  intros l.
  remember (selectEvens l) as c eqn:Heqc. symmetry in Heqc.
  induction l.
  - intros l HInaselect. simpl in Heqc. subst. destruct HInaselect.
  - simpl in Heqc.
    intros x HInaselect.
    destruct (even a) eqn:E.
    * rewrite <- Heqc in HInaselect.
      destruct HInaselect.
      + subst. now left.
      + right.
  *)
  induction l.
  - simpl. auto.
  - simpl.
    intros b H.
    destruct (even a) eqn:E.
    + destruct H.
      * subst. now left.
      * right. apply IHl. apply H.
    + right. apply IHl. auto.
  Qed.
  
(*
Theorem selectEvensIndPreservesSorted :
  forall l selected, selectEvensInd l selected -> LocallySorted le l -> LocallySorted le selected.
Proof.
  (*
  intros l selected H.
  induction H.
  - auto.
  - intros Hsorted.
    inversion Hsorted; subst.
    * Print LocallySorted.
    constructor.
    * apply IHselectEvensInd. auto.
    * 
    apply IHselectEvensInd in H3.
    constructor.
  *)
  (*
  intros l selected H Hsorted. generalize dependent H. generalize dependent selected.
  induction Hsorted; intros selected Hselect.
  - inversion Hselect. constructor.
  - inversion Hselect; subst.
    + inversion H1; subst. constructor.
    + inversion H1; subst. constructor.
  - inversion Hselect; subst.
    + inversion H2; subst.
      * constructor.
        -- apply IHHsorted. apply H2.
        -- assumption.
      * specialize (IHHsorted _ H2).
        inversion IHHsorted; subst.
        -- constructor.
        --  
  *)
  (*
  intros l. induction l.
  - intros ? Hsel ?. inversion Hsel; subst. constructor.
  - intros selected Hsel Hsor.
    inversion Hsor; subst.
    + apply IHl.
      * 
  *)
  intros l selected. generalize dependent l.
  induction selected.
  - intros l Hsel Hsor. constructor.
  - intros l Hsel  Hsor.
    inversion Hsel; subst.
    + inversion Hsor; subst.
      * inversion H2; subst. constructor.
      * specialize (IHselected _ H2 H1).
        inversion H2; subst.
        -- constructor; try assumption.
        -- *)


Theorem selectEvensInd_preserves_forall :
  forall f l select, selectEvensInd l select -> Forall f l -> Forall f select.
Proof.
  intros f l select Hsel.
  induction Hsel; intros Hfor.
  - assumption.
  - inversion Hfor; subst.
    constructor; try auto.
  - inversion Hfor; subst. auto.
  Qed.  

Theorem selectEvensIndPreservesSorted :
  forall l selected, selectEvensInd l selected -> StronglySorted le l -> StronglySorted le selected.
Proof.
  (*
  intros l. induction l; simpl; intros selected Hsel Hsor.
  - inversion Hsel; subst. constructor.
  - inversion Hsel; subst; inversion Hsor; subst.
    + specialize (IHl _ H1 H2).
      constructor; try assumption.
  *)
  intros l selected Hsel Hsor. generalize dependent Hsel. generalize dependent selected.
  induction Hsor; intros selected Hsel.
  - inversion Hsel; subst. constructor.
  - inversion Hsel; subst.
    + constructor.
      * apply IHHsor. assumption.
      * apply selectEvensInd_preserves_forall with l; auto.
    + now apply IHHsor.
  Qed.
