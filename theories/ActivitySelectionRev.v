
From Coq Require Import Sorting.Sorted.
From Coq Require Import Lists.List.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import Lia.

From Playground Require Import NonEmptyList.

Import ListNotations.


Record Activity : Set := mkActivity
 { start : nat
 ; finish : nat
 ; start_before_finish : start < finish
 }.

Example example_act_1_proof : 0 < 6. Proof. lia. Qed.
Example example_act_2_proof : 1 < 4. Proof. auto. Qed.
Example example_act_3_proof : 2 < 14. Proof. lia. Qed.
Example example_act_4_proof : 3 < 5. Proof. auto. Qed.
Example example_act_5_proof : 3 < 9. Proof. lia. Qed.
Example example_act_6_proof : 5 < 7. Proof. auto. Qed.
Example example_act_7_proof : 5 < 9. Proof. auto. Qed.
Example example_act_8_proof : 6 < 10. Proof. auto. Qed.
Example example_act_9_proof : 8 < 11. Proof. auto. Qed.
Example example_act_10_proof : 8 < 12. Proof. auto. Qed.
Example example_act_11_proof : 12 < 16. Proof. auto. Qed.

Example example_act_1 : Activity := {| start_before_finish := example_act_1_proof |}.
Example example_act_2 : Activity := {| start_before_finish := example_act_2_proof |}.
Example example_act_3 : Activity := {| start_before_finish := example_act_3_proof |}.
Example example_act_4 : Activity := {| start_before_finish := example_act_4_proof |}.
Example example_act_5 : Activity := {| start_before_finish := example_act_5_proof |}.
Example example_act_6 : Activity := {| start_before_finish := example_act_6_proof |}.
Example example_act_7 : Activity := {| start_before_finish := example_act_7_proof |}.
Example example_act_8 : Activity := {| start_before_finish := example_act_8_proof |}.
Example example_act_9 : Activity := {| start_before_finish := example_act_9_proof |}.
Example example_act_10 : Activity := {| start_before_finish := example_act_10_proof |}.
Example example_act_11 : Activity := {| start_before_finish := example_act_11_proof |}.

Example example_activities : list Activity :=
  [ example_act_1
  ; example_act_2
  ; example_act_3
  ; example_act_4
  ; example_act_5
  ; example_act_6
  ; example_act_7
  ; example_act_8
  ; example_act_9
  ; example_act_10
  ; example_act_11
  ].
  
Example example_compatible_activities : list Activity :=
  [ example_act_4
  ; example_act_6
  ; example_act_10
  ; example_act_11
  ].

Definition FinishBE (a b : Activity): Prop := finish a <= finish b.

About FinishBE.



Fixpoint selectCompatibleActivitiesNE (l : non_empty_list Activity) : non_empty_list Activity :=
  match l with
  | NonEmptyListSingle h => NonEmptyListSingle h
  | NonEmptyList newAct ts => 
      match selectCompatibleActivitiesNE ts with
      | NonEmptyListSingle onlySelected =>
          if finish newAct <=? start onlySelected then
            NonEmptyList newAct (NonEmptyListSingle onlySelected)
          else
            NonEmptyListSingle onlySelected
      | NonEmptyList firstSelected selected => 
          if finish newAct <=? start firstSelected then
            NonEmptyList newAct (NonEmptyList firstSelected selected)
          else
            NonEmptyList firstSelected selected
      end
  end.

Definition selectCompatibleActivities (l : list Activity) : list Activity :=
  match l with
  | [] => []
  | h :: t => non_empty_list_to_list (selectCompatibleActivitiesNE (list_to_non_empty_list h t))
  end.
  
Check selectCompatibleActivities example_activities = example_compatible_activities.

Inductive selectCompatibleActivitiesInd : list Activity -> list Activity -> Prop :=
  | SelectCompatibleActivitiesEmpty : selectCompatibleActivitiesInd [] []
  | SelectCompatibleActivitiesSingle: forall act, selectCompatibleActivitiesInd [act] [act]
  | SelectCompatibleActivitiesInclude :
      forall newAct acts lastSelected selected, 
      finish newAct <= start lastSelected ->
      selectCompatibleActivitiesInd acts (lastSelected :: selected) ->
      selectCompatibleActivitiesInd (newAct :: acts) (newAct :: lastSelected :: selected)
  | SelectCompatibleActivitiesSkip :
      forall skippedAct acts selected,
      selectCompatibleActivitiesInd acts selected ->
      selectCompatibleActivitiesInd (skippedAct :: acts) selected
  .

Example finish_example_6_10 : finish example_act_6 <= start example_act_10. Proof. simpl. lia. Qed.

Example selectCompatibleActivitiesInd_example1 :
    selectCompatibleActivitiesInd
      [ example_act_5; example_act_6; example_act_8; example_act_10]
      [example_act_6; example_act_10] :=
  SelectCompatibleActivitiesSkip _ _ _ (
  SelectCompatibleActivitiesInclude _ _ _ _ finish_example_6_10 (
  SelectCompatibleActivitiesSkip _ _ _ (
  SelectCompatibleActivitiesSingle _
  )))
  .
  
Example selectCompatibleActivitiesInd_example2 :
    selectCompatibleActivitiesInd
      [ example_act_5; example_act_6; example_act_8; example_act_10]
      [example_act_6; example_act_10].
Proof.
  apply SelectCompatibleActivitiesSkip.
  apply SelectCompatibleActivitiesInclude. { simpl. lia. }
  apply SelectCompatibleActivitiesSkip.
  constructor.
Qed.

Example selectCompatibleActivitiesInd_example3 :
    selectCompatibleActivitiesInd example_activities example_compatible_activities.
Proof.
  apply SelectCompatibleActivitiesSkip.
  apply SelectCompatibleActivitiesSkip.
  apply SelectCompatibleActivitiesSkip.
  apply SelectCompatibleActivitiesInclude. { simpl. lia. }
  apply SelectCompatibleActivitiesSkip.
  apply SelectCompatibleActivitiesInclude. { simpl. lia. }
  apply SelectCompatibleActivitiesSkip.
  apply SelectCompatibleActivitiesSkip.
  apply SelectCompatibleActivitiesSkip.
  apply SelectCompatibleActivitiesInclude. { simpl. lia. }
  constructor.
Qed.

Lemma some_selects_means_some_acts :
  forall acts lastSelected selected,
  selectCompatibleActivitiesInd acts (lastSelected :: selected) ->
  length acts <> 0.
Proof.
  intros acts lastSelected selected H.
  inversion H; subst; simpl; auto.
  Qed.

Lemma non_empty_list_is_single :
  forall A (a b : A) acts, list_to_non_empty_list a acts = NonEmptyListSingle b -> a = b /\ acts = [].
Proof.
  destruct acts; simpl; intros H.
  - now inversion H.
  - now inversion H.
  Qed.

Lemma non_empty_list_is_list :
  forall A l nel (a b : A),
  list_to_non_empty_list a l = NonEmptyList b nel ->
  a = b /\ (exists x l', l = x :: l' /\ list_to_non_empty_list x l' = nel).
Proof.
  intros ? l. induction l.
  - simpl. intros. inversion H.
  - simpl. intros. inversion H; subst. split; auto.
    now exists a,l.
  Qed.

Lemma non_empty_to_list :
  forall A x l (a : A), non_empty_list_to_list x = (a :: l) -> x = list_to_non_empty_list a l.
Proof.
  (*
  intros A x. induction x.
  - simpl. intros. now inversion H; subst.
  - simpl. intros. inversion H; subst.
    destruct x; simpl.
  *)
  intros A x l. generalize dependent x.
  induction l; simpl; intros.
  - destruct x; auto.
    + simpl in H. inversion H. now subst.
    + simpl in H. inversion H; subst.
      destruct x. simpl in H2. discriminate. simpl in H2. discriminate.
  - destruct x eqn:E.
    + simpl in H. discriminate.
    + simpl in H. inversion H; subst.
      specialize (IHl _ _ H2). now subst.
  Qed. 

Theorem selectCompat_plus_one_more_compat2 :
  forall l lastSelected selected a,
  selectCompatibleActivities l = lastSelected :: selected ->
  finish a <= start lastSelected ->
  selectCompatibleActivities (a :: l) = a :: lastSelected :: selected.
Proof.
  intros l lastSelected selected a Hsel Hfin.
  destruct l,selected; try discriminate; simpl in *.
  - assert
      (Hselrewrite: selectCompatibleActivitiesNE (list_to_non_empty_list a0 l) = 
        list_to_non_empty_list lastSelected []).
    { now apply non_empty_to_list in Hsel. }
    rewrite Hselrewrite; simpl.
    now rewrite (leb_correct _ _ Hfin); simpl.
  - assert
      (Hselrewrite: selectCompatibleActivitiesNE (list_to_non_empty_list a0 l) = 
        list_to_non_empty_list lastSelected (a1 :: selected)).
    { now apply non_empty_to_list in Hsel. }
    rewrite Hselrewrite; simpl.
    rewrite (leb_correct _ _ Hfin); simpl.
    now rewrite undo_non_empty_to_list.
  Qed.

Theorem selectCompatibleActivities_from_selectCompatibleActivitiesInd : forall l selected,
  selectCompatibleActivitiesInd l selected -> selectCompatibleActivities l = selected.
Proof.
  induction l.
  - simpl. intros selected H. now inversion H; subst.
  - intros selected Hsel.
    inversion Hsel; subst; auto.
    + specialize (IHl _ H3).
      simpl.
      rewrite <- IHl in *.
      simpl.


  (* unfold selectCompatibleActivities. *)
  (*
  intros l selected H.
  induction H; auto.
  - simpl.
    assert (Hacts: length acts <> 0).
    { now apply some_selects_means_some_acts with (selected := selected) (lastSelected := lastSelected). }
    destruct acts; try discriminate; clear Hacts.
    unfold selectCompatibleActivities in IHselectCompatibleActivitiesInd.
    change (list_to_non_empty_list newAct (a :: acts)) with (NonEmptyList newAct (list_to_non_empty_list a acts)).
    rewrite <- IHselectCompatibleActivitiesInd.
    simpl.
    
    unfold list_to_non_empty_list. simpl.
    simpl.
    destruct (list_to_non_empty_list a acts) eqn:E; simpl.
    * simpl in IHselectCompatibleActivitiesInd.
      apply non_empty_list_is_single in E. destruct E; subst.
      inversion IHselectCompatibleActivitiesInd; subst. clear IHselectCompatibleActivitiesInd. 
      now rewrite (leb_correct _ _ H).
    * apply non_empty_list_is_list in E. destruct E. destruct H2. destruct H2. destruct H2; subst.
      simpl. unfold selectCompatibleActivitiesNE in IHselectCompatibleActivitiesInd.
      fold selectCompatibleActivitiesNE in *.
      destruct (list_to_non_empty_list x x0) eqn:F.
      + simpl in *.
        apply non_empty_list_is_single in F. destruct F; subst.
        simpl in *.
  *)
        
(*

Inductive selectCompatibleActivitiesInd : list Activity -> list Activity -> Prop :=
  | SelectCompatibleActivitiesEmpty : selectCompatibleActivitiesInd [] []
  | SelectCompatibleActivitiesSingle : forall act, selectCompatibleActivitiesInd [act] [act]
  | SelectCompatibleActivitiesInclude :
      forall lastSelected acts newAct selected, 
      finish lastSelected <= start newAct ->
      selectCompatibleActivitiesInd acts (selected ++ [lastSelected]) ->
      selectCompatibleActivitiesInd (acts ++ [newAct]) (selected ++ [lastSelected] ++ [newAct])
  | SelectCompatibleActivitiesSkip :
      forall skippedAct acts selected, 
      selectCompatibleActivitiesInd acts selected ->
      selectCompatibleActivitiesInd (acts ++ [skippedAct]) selected
  .

Example finish_example_1_4 : finish example_act_1 <= start example_act_4. Proof. simpl. lia. Qed.

Example selectCompatibleActivitiesInd_example1 :
    selectCompatibleActivitiesInd
      [example_act_1; example_act_2; example_act_3; example_act_4; example_act_5]
      [example_act_1; example_act_4] :=
  SelectCompatibleActivitiesSkip _ _ _ (
  SelectCompatibleActivitiesInclude example_act_1 _ example_act_4 [] finish_example_1_4 (
  SelectCompatibleActivitiesSkip _ _ _ (
  SelectCompatibleActivitiesSkip _ _ _ (
  SelectCompatibleActivitiesSingle _
  )))).
  
Lemma append_something_ne_nil : forall A (a : A) l, l ++ [a] = [] -> False.
Proof.
  intros A a l. induction l.
  - simpl. intro Contra. discriminate.
  - simpl. intro Contra. discriminate.
  Qed.

Example selectCompatibleActivitiesInd_example2 :
  selectCompatibleActivitiesInd [] [example_act_1] -> False.
Proof.
  intros H. inversion H; subst.
  - now apply append_something_ne_nil in H0.
  - now apply append_something_ne_nil in H0.
  Qed.

(* TODO: Rewrite everything here by building up the compatible activities in selectCompatibleActivities
   in reverse, so we build up a normal list. *)

(*
Theorem selectCompatibleActivities_equal : forall l selected,
  selectCompatibleActivitiesInd l selected -> selectCompatibleActivities l = selected.
Proof.
  unfold selectCompatibleActivities.
  intros l selected H. induction H; auto.
  -
  
*) 

Print list_ind.

Definition list_ind2 : forall (A : Type) (P : list A -> Prop),
    P [] ->
    (forall a, P [a]) ->
    (forall a b l, P l -> P (a :: b :: l)) ->
    forall l, P l :=
  fun _ _ Hnil Hsing H =>
    fix F l :=
      match l with
      | [] => Hnil
      | [a] => Hsing a
      | (a :: b :: ts) => H a b ts (F ts)
      end.

Theorem all_compatible_in_orig_list : forall l a, In a (selectCompatibleActivities l) -> In a l.
Proof.
  (*
  unfold selectCompatibleActivities.
  induction l.
  - simpl. auto.
  - simpl. intros a0 H.
    destruct H.
    + left. auto.
    + simpl in H.
  *)
  (*
  intros l a H.
  remember (selectCompatibleActivities l) as c.
  destruct (selectCompatibleActivities l).
  - simpl in H. subst. destruct H.
  - subst. simpl in H. destruct H.
    +  
  *)
  (* intros l. induction l using list_ind2.
  - auto.
  - simpl. auto.
  - simpl. intros. destruct H.
    + auto.
    + destruct (finish a <=? start b) eqn:E.
      * *)
  unfold selectCompatibleActivities.
  intros l a H. induction l.
  - auto.
  - unfold selectCompatibleActivities' in H. fold selectCompatibleActivities' in H.
    assert (0 <=? start a0 = true).
    { auto. }
    rewrite H0 in H.
    simpl in H.
    destruct H.
    + subst. now constructor.
    + Admitted.

(* TODO: Try to build an inductive datatype representing selectCompatibleActivities! *)
  

Theorem selectCompatibleActivitiesSorted :
  forall l, StronglySorted FinishBE l -> StronglySorted FinishBE (selectCompatibleActivities l).
Proof.
  (*
  intros l H. induction H; subst.
  - unfold selectCompatibleActivities. simpl. constructor.
  - unfold selectCompatibleActivities in *. simpl.
    apply SSorted_cons.
    * inversion IHStronglySorted.
      + admit.
      + subst. unfold selectCompatibleActivities'.
    * *)
  (*
  intros l. induction l.
  - unfold selectCompatibleActivities. simpl. auto.
  - unfold selectCompatibleActivities in *. simpl in *.
    intro H. constructor.
    * inversion H; subst. clear H. apply IHl in H2.
      unfold selectCompatibleActivities'.
      destruct l.
      + constructor.
      + simpl. fold selectCompatibleActivities'.
  *)
  (*
  unfold selectCompatibleActivities.
  unfold selectCompatibleActivities'.
  induction l.
  - auto.
  - assert (forall n, 0 <=? n = true) by (destruct n; auto).
    rewrite H. clear H. fold selectCompatibleActivities' in *.
    intro H.
    inversion H; subst. clear H. specialize (IHl H2).
    constructor.
    induction l.
    + admit.
    + unfold selectCompatibleActivities'.
  *)
  (*
  unfold selectCompatibleActivities.
  intros l.
  induction l using list_ind2.
  - simpl. auto.
  - simpl. auto.
  - simpl. intros H.
    inversion H; subst. inversion H3; subst.
    unfold FinishBE in H4.
    inversion H2; subst.
    specialize (IHl H6).
  *)
  unfold selectCompatibleActivities.
  intros l H. induction H; subst.
  - simpl. constructor. 
  - simpl. constructor.
    + inversion IHStronglySorted; subst.
      * admit.
      * Admitted. 
      
*)