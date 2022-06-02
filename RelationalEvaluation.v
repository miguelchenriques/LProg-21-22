From FirstProject Require Import Maps Imp.
From Coq Require Import Lists.List. Import ListNotations.

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".


(* ================================================================= *)
(** ** Evaluation as a Relation *)

(** We'll use the notation [st1 / q1 =[ c ]=> st2 / q2 / r] for the [ceval] relation:
    [st1 / q1 =[ c ]=> st2 / q2 / r] means that executing program [c] in a starting
    state [st1] with continuations [q1] results in an ending state [st2] with unexplored
    continuations [q2]. Moreover the result of the computation will be [r].*)

(* Type of result *)
Inductive result : Type :=
| Success
| Fail.

(* Notation that we use *)
Reserved Notation "st1 '/' q1 '=[' c ']=>' st2 '/' q2 '/' r"
(at level 40,
 q1 constr at next level,
 c custom com at level 99, 
 st2 constr at next level,
 q2 constr at next level,
 r constr at next level).

(* 
3. TODO: Define the relational semantics (ceval) to support the required constructs.
*)

Inductive ceval : com -> state -> list (state * com) -> 
          result -> state -> list (state * com) -> Prop :=
| E_Skip : forall st q,
 st / q =[ skip ]=> st / q / Success

| E_Asgn : forall st q a n x,
 aeval st a = n ->
 st / q =[ x := a ]=> (x !-> n ; st) / q / Success

| E_Seq : forall c1 c2 st st' st'' q q' q'' r,
 st / q =[ c1 ]=> st' / q' / Success ->
 st' / q' =[ c2 ]=> st'' / q'' / r ->
 st / q =[ c1 ; c2 ]=> st'' / q'' / r

| E_SeqFail : forall c1 c2 st st' q q',
 st / q =[ c1 ]=> st' / q' / Fail ->
 st / q =[ c1 ; c2 ]=> st' / q' / Fail

| E_IfTrue : forall st st' b c1 c2 q q' r,
 beval st b = true ->
 st / q =[ c1 ]=> st' / q' / r ->
 st / q =[ if b then c1 else c2 end ]=> st' / q' / r

| E_IfFalse : forall st st' b c1 c2 q q' r,
 beval st b = false -> 
 st / q =[ c2 ]=> st' / q' / r ->
 st / q =[ if b then c1 else c2 end ]=> st' / q' / r

| E_WhileFalse : forall b st c q,
 beval st b = false ->
 st / q =[ while b do c end ]=> st / q / Success

| E_WhileTrue : forall st st' st'' q q' q'' b c,
 beval st b = true ->
 st / q =[ c ]=> st' / q' / Success ->
 st' / q' =[ while b do c end ]=> st'' / q'' / Success ->
 st / q =[ while b do c end ]=> st'' / q'' / Success 

| E_ChoiceLeft : forall st q c1 c2 st' q' r,
 st / q =[ c1 ]=> st' / q' / r ->
 st / q =[ c1 !! c2 ]=> st' / ((st, c2) :: q') / r 

| E_ChoiceRight : forall st q c1 c2 st' q' r,
 st / q =[ c2 ]=> st' / q' / r ->
 st / q =[ c1 !! c2 ]=> st' / ((st, c1) :: q') / r 

| E_GuardTrue : forall st q c st' q' b r,
 beval st b = true ->
 st / q =[ c ]=> st' / q' / r ->
 st / q =[ b -> c ]=> st' / q' / r 

| E_GuardFalseEmpty : forall st q c b st',
 beval st b = false ->
 q = [] ->
 st / q =[ b -> c ]=> st' / [] / Fail

| E_GuardFalseCont : forall st q c c' q' st' st'' b r,
 beval st b = false ->
 st' / q =[ c' ; b -> c ]=> st'' / q' / r ->
 st / ((st', c') :: q) =[ b -> c ]=> st'' / q' / r

(* TODO. Hint: follow the same structure as shown in the chapter Imp *)
where "st1 '/' q1 '=[' c ']=>' st2 '/' q2 '/' r" := (ceval c st1 q1 r st2 q2).


(**
  3.1. TODO: Use the new relational semantics to prove the examples
             ceval_example_if, ceval_example_guard1, ceval_example_guard2,
             ceval_example_guard3 and ceval_example_guard4.
*)

Example ceval_example_if:
empty_st / [] =[
X := 2;
if (X <= 1)
  then Y := 3
  else Z := 4
end
]=> (Z !-> 4 ; X !-> 2) / [] / Success.
Proof.
  apply E_Seq with (X !-> 2) [].
  - apply E_Asgn. reflexivity.
  - apply E_IfFalse. reflexivity. apply E_Asgn. reflexivity.
Qed.


Example ceval_example_guard1:
empty_st / [] =[
   X := 2;
   (X = 1) -> X:=3
]=> (empty_st) / [] / Fail.
Proof.
  apply E_Seq  with (X !-> 2) [].
    - apply E_Asgn. reflexivity.
    - apply E_GuardFalseEmpty. reflexivity. reflexivity.
Qed. 

Example ceval_example_guard2:
empty_st / [] =[
   X := 2;
   (X = 2) -> X:=3
]=> (X !-> 3 ; X !-> 2) / [] / Success.
Proof.
  apply E_Seq with (X !-> 2) [].
    - apply E_Asgn. reflexivity.
    - apply E_GuardTrue.
      -- reflexivity.
      -- apply E_Asgn. reflexivity.
Qed.

Example ceval_example_guard3: exists q,
empty_st / [] =[
   (X := 1 !! X := 2);
   (X = 2) -> X:=3
]=> (X !-> 3) / q / Success.
Proof.
  eexists.
  apply E_Seq with (X !-> 1) [(empty_st, <{ X:=2 }>)].
    - apply E_ChoiceLeft. apply E_Asgn. reflexivity.
    - apply E_GuardFalseCont. reflexivity.
      apply E_Seq with ( X!->2) [].
      -- apply E_Asgn. reflexivity.
      -- replace (X !-> 3) with (X !-> 3; X!->2).  --- apply E_GuardTrue. reflexivity. apply E_Asgn. reflexivity. --- apply t_update_shadow.
Qed.
    
Example ceval_example_guard4: exists q,
empty_st / [] =[
   (X := 1 !! X := 2);
   (X = 2) -> X:=3
]=> (X !-> 3) / q / Success.
Proof.
  eexists.
  apply E_Seq with (X !-> 2) [(empty_st, <{ X:=1 }>)].
    - apply E_ChoiceRight. apply E_Asgn. reflexivity.
    - apply E_GuardTrue. reflexivity.
      replace (X !-> 3) with (X !-> 3; X!->2). apply E_Asgn. reflexivity. apply t_update_shadow.
Qed.



(* 3.2. Behavioral equivalence *)

Definition cequiv_imp (c1 c2 : com) : Prop := 
forall (st1 st2 : state) q1 q2 result,
(st1 / q1 =[ c1 ]=> st2 / q2 / result) ->
exists q3, 
(st1 / q1 =[ c2 ]=> st2 / q3 / result).

Definition cequiv (c1 c2 : com) : Prop :=
cequiv_imp c1 c2 /\ cequiv_imp c2 c1.

Infix "==" := cequiv (at level 99).


(**
  3.2. TODO: Prove the properties below.
*)

Lemma cequiv_ex1:
<{ X := 2; X = 2 -> skip }> == 
<{ X := 2 }>.
Proof.
  split; unfold cequiv_imp; intros; eexists.
    -  inversion H; subst. inversion H2; subst. inversion H8; subst; try discriminate; inversion H10; subst.
        -- apply E_Asgn. reflexivity.
        -- inversion H7; subst.
    - inversion H; subst. eapply E_Seq; try discriminate.
      -- apply E_Asgn. reflexivity.
      -- apply E_GuardTrue.
        --- reflexivity.
        --- apply E_Skip. 
Qed.

(*
Lemma cequiv_ex2:
<{ (X := 1 !! X := 2); X = 2 -> skip }> == 
<{ X := 2 }>.
Proof.
  split; unfold cequiv_imp; intros; eexists.
    - inversion H; subst. inversion H2; subst. inversion H8; subst; inversion H10; subst; try discriminate. 
      -- inversion H11; subst. inversion H4; subst; try discriminate.
        --- inversion H13; subst; try discriminate. inversion H15; subst. apply E_Asgn. reflexivity.
        --- inversion H12.
      -- inversion H10; subst; try discriminate. admit.
      -- inversion H7; subst. admit.
Admitted.
*)


Lemma choice_idempotent: forall c,
<{ c !! c }> == <{ c }>.
Proof.
  split; intros st1 st2 q1 q2 result H.
    - inversion H; subst; try discriminate.
      -- eexists. apply H7.
      -- eexists. apply H7.
    - eexists. apply E_ChoiceLeft. apply H.
Qed.

Lemma choice_comm: forall c1 c2,
<{ c1 !! c2 }> == <{ c2 !! c1 }>.
Proof.
  split; intros st1 st2 q1 q2 result H.
    - inversion H; subst.
      -- eexists. apply E_ChoiceRight. apply H7.
      -- eexists. apply E_ChoiceLeft. apply H7.
    - inversion H; subst.
      -- eexists. apply E_ChoiceRight. apply H7.
      -- eexists. apply E_ChoiceLeft. apply H7.
Qed.

Lemma choice_assoc: forall c1 c2 c3,
<{ (c1 !! c2) !! c3 }> == <{ c1 !! (c2 !! c3) }>.
Proof.
  split; intros st1 st2 q1 q2 result H.
    - inversion H; subst.
      -- inversion H7; subst.
        --- eexists. apply E_ChoiceLeft. apply H8.
        --- eexists. apply E_ChoiceRight. apply E_ChoiceLeft. apply H8.
      -- eexists. apply E_ChoiceRight. apply E_ChoiceRight. apply H7.
    - inversion H; subst.
      -- eexists. apply E_ChoiceLeft. apply E_ChoiceLeft. apply H7.
      -- inversion H7; subst.
        --- eexists. apply E_ChoiceLeft. apply E_ChoiceRight. apply H8.
        --- eexists. apply E_ChoiceRight. apply H8.
Qed.


Lemma choice_seq_distr_l: forall c1 c2 c3,
<{ c1 ; (c2 !! c3)}> == <{ (c1;c2) !! (c1;c3) }>.
Proof.
  split; intros st1 st2 q1 q2 result H.
    - inversion H; subst. 
      -- inversion H8; subst.
        --- eexists. apply E_ChoiceLeft. eapply E_Seq.
          ---- apply H2.
          ---- apply H9.
        --- eexists. apply E_ChoiceRight. eapply E_Seq.
          ---- apply H2.
          ---- apply H9.
      -- inversion H; subst.
        --- inversion H9; subst.
          ---- eexists. apply E_ChoiceLeft. eapply E_Seq.
            ----- apply H2.
            ----- apply H10.
          ---- eexists. apply E_ChoiceRight. eapply E_Seq.
            ----- apply H2.
            ----- apply H10.
        --- eexists. apply E_ChoiceLeft. eapply E_SeqFail. apply H7.
    - inversion H; subst.
      -- inversion H7; subst. 
        --- eexists. eapply E_Seq.
          ---- apply H2.
          ---- apply E_ChoiceLeft. apply H9.
        --- eexists. apply E_SeqFail. apply H8.
     -- inversion H7; subst.
       --- eexists. eapply E_Seq.
        ---- apply H2.
        ---- apply E_ChoiceRight. apply H9.
      --- eexists. eapply E_SeqFail. apply H8.
Qed.

Lemma choice_congruence: forall c1 c1' c2 c2',
c1 == c1' -> c2 == c2' ->
<{ c1 !! c2 }> == <{ c1' !! c2' }>.
Proof.
  (* TODO *)
Qed.