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
| E_Seq : forall c1 c2 st st' st'' q q' q'',
 st / q =[ c1 ]=> st' / q' / Success ->
 st' / q' =[ c2 ]=> st'' / q'' / Success ->
 st / q =[ c1 ; c2 ]=> st'' / q'' / Success
| E_IfTrue : forall st st' b c1 c2,
 beval st b = true ->
 st / q =[ c1 ]=> st' / q' / Success ->
 st / q =[ if b then c1 else c2 end ]=> st' / q' / Success
| E_IfFalse : forall st st' b c1 c2,
 beval st b = false -> 
 st / q =[ c2 ]=> st' / q' / Success ->
 st / q =[ if b then c1 else c2 end ]=> st' / q' / Success
| E_WhileFalse : forall b st c q,
 beval st b = false ->
 st / q =[ while b do c end ]=> st / q / Success
| E_WhileTrue : forall st st' st'' q q' q'' b c,
 beval st b = true ->
 s /t q =[ c ]=> st' / q' / Success ->
 st' / q' =[ while b do c end ]=> st'' / q'' / Success ->
 st / q =[ while b do c end ]=> st'' / q'' / Success 
| E_ChoiceLeft : forall st q c1 c2 st' q',
 st / q =[ c1 ]=> st' / q' / Success ->
 st / q =[ c1 !! c2 ]=> st' / ((st, c2) :: q) / Success
| E_ChoiceRight : forall st q c1 c2 st' q',
 st / q =[ c1 ]=> st' / q' / Success ->
 st / q =[ c1 !! c2 ]=> st' / ((st, c2) :: q) / Success
| E_GuardTrue : forall st q c st' q' b,
 if beval st b = true ->
 st / q =[ c ]=> st' / q' / Success ->
 st / q =[ b -> c ]=> st' / q' / Success
| E_GuardFalseEmpty : forall st q c st' q' b,
 if beval st b = false ->
 q = [] ->
 st / q =[ b -> c ] st / q / Fail
| E_GuardFalseCont : forall st q c c2 st' st'' q' q'' b,
 if beval st b = false ->
 q = (st' c2) :: q' ->
 st' / q' =[ c2 ] st'' / q'' / Success ->
 st / q =[ b -> c ]=> st'' / q'' / success


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
  (* TODO *)
Qed.


Example ceval_example_guard1:
empty_st / [] =[
   X := 2;
   (X = 1) -> X:=3
]=> (empty_st) / [] / Fail.
Proof.
  (* TODO *)
Qed. 

Example ceval_example_guard2:
empty_st / [] =[
   X := 2;
   (X = 2) -> X:=3
]=> (X !-> 3 ; X !-> 2) / [] / Success.
Proof.
  (* TODO *)
Qed. 

Example ceval_example_guard3: exists q,
empty_st / [] =[
   (X := 1 !! X := 2);
   (X = 2) -> X:=3
]=> (X !-> 3) / q / Success.
Proof.
  (* TODO *)
Qed.
    
Example ceval_example_guard4: exists q,
empty_st / [] =[
   (X := 1 !! X := 2);
   (X = 2) -> X:=3
]=> (X !-> 3) / q / Success.
Proof.
  (* TODO *)
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
  (* TODO *)
Qed.

Lemma cequiv_ex2:
<{ (X := 1 !! X := 2); X = 2 -> skip }> == 
<{ X := 2 }>.
Proof.
  (* TODO *)
Qed.


Lemma choice_idempotent: forall c,
<{ c !! c }> == <{ c }>.
Proof.
  (* TODO *)
Qed.

Lemma choice_comm: forall c1 c2,
<{ c1 !! c2 }> == <{ c2 !! c1 }>.
Proof.
  (* TODO *)
Qed.

Lemma choice_assoc: forall c1 c2 c3,
<{ (c1 !! c2) !! c3 }> == <{ c1 !! (c2 !! c3) }>.
Proof.
  (* TODO *)
Qed.


Lemma choice_seq_distr_l: forall c1 c2 c3,
<{ c1 ; (c2 !! c3)}> == <{ (c1;c2) !! (c1;c3) }>.
Proof.
  (* TODO *)
Qed.

Lemma choice_congruence: forall c1 c1' c2 c2',
c1 == c1' -> c2 == c2' ->
<{ c1 !! c2 }> == <{ c1' !! c2' }>.
Proof.
  (* TODO *)
Qed.