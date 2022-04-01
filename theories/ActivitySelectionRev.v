
From Coq Require Import Sorting.Sorted.
From Coq Require Import Lists.List.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import Lia.

From Playground Require Import NonEmptyList.

Import ListNotations.

(*
Definition exa : Prop := forall (x y : nat), nat -> S x = x.

Check forall x, S x = x -> nat.

Definition exb : Prop -> Prop := fun p => forall (x y : nat), nat -> S x = x -> p.

Check exb.

Definition exc : Type := forall (x : nat), Prop -> nat.
*)

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
      forall skippedAct acts lastSelected selected,
      finish skippedAct > start lastSelected ->
      selectCompatibleActivitiesInd acts (lastSelected :: selected) ->
      selectCompatibleActivitiesInd (skippedAct :: acts) (lastSelected :: selected)
  .

Example finish_example_6_10 : finish example_act_6 <= start example_act_10. Proof. simpl. lia. Qed.
Example finish_example_8_10 : finish example_act_8 > start example_act_10. Proof. simpl. lia. Qed.
Example finish_example_5_6 : finish example_act_5 > start example_act_6. Proof. simpl. lia. Qed.

Example selectCompatibleActivitiesInd_example1 :
    selectCompatibleActivitiesInd
      [ example_act_5; example_act_6; example_act_8; example_act_10]
      [example_act_6; example_act_10] :=
  SelectCompatibleActivitiesSkip _ _ _ _ finish_example_5_6 (
  SelectCompatibleActivitiesInclude _ _ _ _ finish_example_6_10 (
  SelectCompatibleActivitiesSkip _ _ _ _ finish_example_8_10 (
  SelectCompatibleActivitiesSingle _
  )))
  .
  
Example selectCompatibleActivitiesInd_example2 :
    selectCompatibleActivitiesInd
      [ example_act_5; example_act_6; example_act_8; example_act_10]
      [example_act_6; example_act_10].
Proof.
  apply SelectCompatibleActivitiesSkip. { simpl. lia. }
  apply SelectCompatibleActivitiesInclude. { simpl. lia. }
  apply SelectCompatibleActivitiesSkip. { simpl. lia. }
  constructor.
Qed.

Example selectCompatibleActivitiesInd_example3 :
    selectCompatibleActivitiesInd example_activities example_compatible_activities.
Proof.
  apply SelectCompatibleActivitiesSkip. { simpl. lia. }
  apply SelectCompatibleActivitiesSkip. { simpl. lia. }
  apply SelectCompatibleActivitiesSkip. { simpl. lia. }
  apply SelectCompatibleActivitiesInclude. { simpl. lia. }
  apply SelectCompatibleActivitiesSkip. { simpl. lia. }
  apply SelectCompatibleActivitiesInclude. { simpl. lia. }
  apply SelectCompatibleActivitiesSkip. { simpl. lia. }
  apply SelectCompatibleActivitiesSkip. { simpl. lia. }
  apply SelectCompatibleActivitiesSkip. { simpl. lia. }
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
  intros A x l. generalize dependent x.
  induction l; simpl; intros.
  - destruct x; auto.
    + simpl in H. inversion H. now subst.
    + simpl in H. inversion H; subst.
      destruct x. simpl in H2. discriminate. simpl in H2. discriminate.
  - destruct x.
    + simpl in H. discriminate.
    + simpl in H. inversion H; subst.
      specialize (IHl _ _ H2). now subst.
  Qed. 
  
Lemma list_to_non_empty :
  forall A x l (a : A), x = list_to_non_empty_list a l -> non_empty_list_to_list x = (a :: l).
Proof.
  intros A x l. generalize dependent x.
  induction l; simpl; intros.
  - subst. auto.
  - subst. simpl. f_equal. now apply IHl.
  Qed.

Theorem selectCompat_plus_one_more_compat :
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
  
Theorem selectCompat_without_one_more_compat :
  forall l lastSelected selected a,
  selectCompatibleActivities l = lastSelected :: selected ->
  finish a > start lastSelected ->
  selectCompatibleActivities (a :: l) = lastSelected :: selected.
Proof.
  intros l lastSelected selected a Hsel Hfin.
  destruct l,selected; try discriminate; simpl in *.
  - assert
      (Hselrewrite: selectCompatibleActivitiesNE (list_to_non_empty_list a0 l) = 
        list_to_non_empty_list lastSelected []).
    { now apply non_empty_to_list in Hsel. }
    rewrite Hselrewrite; simpl.
    assert (Hnotfin: finish a <=? start lastSelected = false).
    { unfold gt in  Hfin. now apply leb_correct_conv. }
    now rewrite Hnotfin.
  - assert
      (Hselrewrite: selectCompatibleActivitiesNE (list_to_non_empty_list a0 l) = 
        list_to_non_empty_list lastSelected (a1 :: selected)).
    { now apply non_empty_to_list in Hsel. }
    rewrite Hselrewrite; simpl.
    rewrite (leb_correct_conv _ _ Hfin); simpl.
    now rewrite undo_non_empty_to_list.
  Qed.

Theorem selectCompatibleActivities_from_selectCompatibleActivitiesInd : forall l selected,
  selectCompatibleActivitiesInd l selected -> selectCompatibleActivities l = selected.
Proof.
  intros l selected H; induction H; auto.
  - apply selectCompat_plus_one_more_compat; auto.
  - apply selectCompat_without_one_more_compat; auto.
  Qed.

(*
Theorem selectCompatActs_one_more_finish_gt : forall l sel a,
  selectCompatibleActivities l = [sel] ->
  finish a > start sel ->
  selectCompatibleActivities (a :: l) = [sel].
Proof.
  induction l; intros sel b Hsel Hfin.
  - simpl in Hsel. discriminate.
  - 
*)

Lemma selectCompatAct_single :
  forall l a sel,
  selectCompatibleActivities (a :: l) = [sel] -> 
  ((a = sel) /\ (l = [])) \/
    ((finish a > start sel) /\ selectCompatibleActivities l = [sel]).
Proof.
  induction l.
  - simpl. intros. inversion H. subst. left. auto.
  - intros b sel H. right. simpl in IHl.
    simpl in H.
    destruct (selectCompatibleActivitiesNE (list_to_non_empty_list a l)) eqn:F.
    + assert (non_empty_list_to_list (selectCompatibleActivitiesNE (list_to_non_empty_list a l)) = [a0]).
      { apply (f_equal non_empty_list_to_list) in F. simpl in F. assumption. }
      specialize (IHl _ _ H0). destruct IHl.
      * destruct H1; subst. simpl in F. simpl in H0. clear H0 F.
        destruct (finish b <=? start a0) eqn:E.
        -- simpl in H. discriminate.
        -- simpl in H. inversion H; subst; clear H. admit.
      * destruct H1. clear H0 F.
        destruct (finish b <=? start a0) eqn:E.
        -- simpl in H. discriminate.
        -- simpl in H. inversion H; subst. clear H. split. admit.
           apply selectCompat_without_one_more_compat; assumption.
    + admit.
  Admitted.

Theorem selCompatAct_from_ne : 
  forall l a selected,
  non_empty_list_to_list (selectCompatibleActivitiesNE (list_to_non_empty_list a l)) = selected ->
  selectCompatibleActivities (a :: l) = selected.
Proof. auto. Qed.

(*
Lemma selectCompatAct_multiple :
  forall l b sel1 sel2 selected,
  selectCompatibleActivities (b :: l) = sel1 :: sel2 :: selected -> 
  or
    ((finish b <= start sel2) /\ selectCompatibleActivities l = sel2 :: selected /\ b = sel1)
    ((finish b > start sel1) /\ selectCompatibleActivities l = sel1 :: sel2 :: selected).
Proof.
  induction l; intros b sel1 sel2 selected.
  - intros. simpl in *. discriminate.
  - intros Hsel.
  
    (* TODO: I think what I'm missing here is a guarantee that the input
       list into selectCompatibleActivities is in order of start times.
       I think selectCompatibleActivitiesInd has this property.
       
       I should prove it! *)
       
    destruct (finish b <=? start sel2) eqn:HFinBleStartSel2.
    * destruct selected.
      + left. split. now apply leb_complete in HFinBleStartSel2.
        apply non_empty_to_list in Hsel.
        simpl in Hsel.
        destruct (selectCompatibleActivitiesNE (list_to_non_empty_list a l)) eqn:E.
        -- assert (finish b <=? start a0 = true).
           { destruct (finish b <=? start a0). auto. inversion Hsel. }
           rewrite H in Hsel. inversion Hsel; subst. clear Hsel.
           admit.
        -- assert (finish b <=? start a0 = false).
           { destruct (finish b <=? start a0); auto. discriminate. }
           rewrite H in Hsel. inversion Hsel; subst. clear Hsel.
           apply (f_equal non_empty_list_to_list) in E. simpl in E.
           apply selCompatAct_from_ne in E.
           specialize (IHl _ _ _ _ E).
           destruct IHl.
           ** destruct H0. destruct H1; subst.
      + 
    
    
    
     left. split. now apply leb_complete in HFinBleStartSel2.
      simpl in Hsel.
      destruct (selectCompatibleActivitiesNE (list_to_non_empty_list a l)) eqn:F.
      + rewrite HFinBleStartSel2 in Hsel.

Theorem selectCompatibleActivitiesInd_from_selectCompatibleActivities : forall l selected,
  selectCompatibleActivities l = selected -> selectCompatibleActivitiesInd l selected.
Proof. 
  induction l as [ | a l IHl].
  - simpl. intros. subst. constructor.
  - destruct selected.
    { admit. }
    destruct selected.
    * intros. apply selectCompatAct_single in H. destruct H.
      + destruct H; subst. constructor.
      + destruct H. specialize (IHl _ H0).
        apply SelectCompatibleActivitiesSkip; assumption.
    * 
*)


(*
Theorem selectCompatibleActivitiesInd_from_selectCompatibleActivities : forall l selected,
  selectCompatibleActivities l = selected -> selectCompatibleActivitiesInd l selected.
Proof. 
  induction l as [ | a1 l IHl];
    destruct selected as [ | sel1 [ | sel2 selected ] ]; intros Hsel.
  - constructor.
  - discriminate.
  - discriminate.
  - admit.
  - destruct l.
    + simpl in Hsel. inversion Hsel. constructor.
    + 
  -  
*)


(*
Theorem selectCompatibleActivitiesInd_from_selectCompatibleActivities : forall l selected,
  selectCompatibleActivities l = selected -> selectCompatibleActivitiesInd l selected.
Proof. 
  induction l as [ | a1 [ | a2 l ] IHl];
    destruct selected as [ | sel1 [ | sel2 selected ] ]; intros Hsel.
  - constructor.
  - discriminate.
  - discriminate.
  - discriminate.
  - inversion Hsel; subst. constructor.
  - discriminate.
  - admit. (* discriminate *)
  - admit.
  - 
*)


 
(*
   simpl in Hsel.
    apply non_empty_to_list in Hsel. simpl in Hsel.
    assert (selectCompatibleActivitiesNE (list_to_non_empty_list a2 l) = NonEmptyListSingle a2).
    { destruct l.
      + reflexivity.
      + assert (forall {A} (x : A) y l, list_to_non_empty_list x (y :: l) = NonEmptyList x (list_to_non_empty_list y l)).
        { now simpl. }
        rewrite H in *.
        destruct (selectCompatibleActivitiesNE (NonEmptyList a2 (list_to_non_empty_list a l))) eqn:E.
        - destruct (finish a1 <=? start a0) eqn:F.
          * discriminate.
          * inversion Hsel; subst. clear Hsel.
            simpl in E.
        simpl in Hsel.
        simpl.
       
  - 
  - destruct selected as [|sel2 selected]; destruct l'.
    + inversion Hsel; subst. constructor.
    + admit.
    + simpl in Hsel. discriminate.
    + destruct (finish act <=? start sel2) eqn:E.
    + simpl in Hsel.
      apply non_empty_to_list in Hsel.
      simpl in *.
      unfold selectCompatibleActivitiesNE in Hsel.
      
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