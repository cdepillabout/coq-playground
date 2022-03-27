
From Coq Require Import Sorting.Sorted.
From Coq Require Import Lists.List.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Init.Nat.
From Coq Require Import Lia.

Import ListNotations.


Record Activity : Set := mkActivity
 { start : nat
 ; finish : nat
 ; start_before_finish : start < finish
 }.

Example example_act_1_proof : 1 < 4. Proof. auto. Qed.
Example example_act_2_proof : 3 < 5. Proof. auto. Qed.
Example example_act_3_proof : 0 < 6. Proof. lia. Qed.
Example example_act_4_proof : 5 < 7. Proof. auto. Qed.
Example example_act_5_proof : 3 < 9. Proof. lia. Qed.
Example example_act_6_proof : 5 < 9. Proof. auto. Qed.
Example example_act_7_proof : 6 < 10. Proof. auto. Qed.
Example example_act_8_proof : 8 < 11. Proof. auto. Qed.
Example example_act_9_proof : 8 < 12. Proof. auto. Qed.
Example example_act_10_proof : 2 < 14. Proof. lia. Qed.
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

Definition FinishBE (a b : Activity): Prop := finish a <= finish b.

About FinishBE.

About Sorted.

(*

Inductive orderedActivities :=
  OrderedActivities : forall (l : list Activity), LocallySorted FinishBE l -> orderedActivities.
  
About Sorted_nil.
  
Definition selectActivitiesAfterFinish
    (fin : nat) (oa : orderedActivities) : orderedActivities :=
  match oa with
  | OrderedActivities l _ => OrderedActivities [] (LSorted_nil FinishBE)
  (*| OrderedActivities l _ => OrderedActivities [] (LSorted_nil FinishBE)
  | OrderedActivities l _ => OrderedActivities [] (LSorted_nil FinishBE)*)
  end.
  
*)

Fixpoint selectCompatibleActivities' (fin : nat) (l : list Activity) : list Activity :=
  match l with
  | [] => []
  | (act :: activities) =>
      if fin <=? start act 
      then act :: selectCompatibleActivities' (finish act) activities
      else selectCompatibleActivities' fin activities
  end.
  
Definition selectCompatibleActivities (l : list Activity) : list Activity :=
  selectCompatibleActivities' 0 l.
  
Compute selectCompatibleActivities example_activities.



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
      *  