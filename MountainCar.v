From RL Require Export TraceThm.

From Coq Require Import
     QArith
     Lia
     Lqa
     List.

From ITree Require Import
     ITree
     ITreeFacts
     Traces.

Import ListNotations.
Import ITreeNotations.
Import MonadNotation.
Open Scope monad_scope.

Definition StateT := prod Q Q.

Inductive ActionT : Type :=
| Left
| Mid
| Right.


(* ref: https://github.com/openai/gym/blob/master/gym/envs/classic_control/mountain_car.py#L20 *)
Definition force := 1#1000.
Definition gravity := 1#400.

Definition min_position := -(6#5).
Definition max_position := 3#5.
Definition max_speed := 7#100.
Definition goal_position := 1#2.

Definition clip (input: Q) (min:Q) (max:Q) :=
  if Qle_bool input  min then min
  else if Qle_bool max input then max
       else input.

(* approximate cos in Q *)
Definition cos (x: Q) :=
  1 - (x^2)/(2#1) + (x^4)/(24#1) - (x^6)/(720#1).

Definition cos_min: forall x : Q, x > -1#1 /\ x < -4#5 -> cos((3#1) * x) < -7#10.
Proof.
Admitted.

Definition max_acc := (7#10) * gravity + (1#1000).

Definition left_most (s: StateT) :=
  match s with
  | (pos, vel) => if Qle_bool vel 0 then pos - (vel * vel) / (2#1) / max_acc else pos
  end.

(* ref: https://github.com/openai/gym/blob/master/gym/envs/classic_control/mountain_car.py#L44 *)
Definition unsafe_env_body : StateT -> ActionT -> StateT :=
  fun state action =>
    let acc :=
        match action with
        | Left => - force
        | Mid => 0
        | Right => force
        end in
    match state with
    | (pos, vel) =>
      let acc' := acc + cos((3#1) * pos) * (-gravity) in
      let vel' := clip (vel + acc') (-max_speed) max_speed in
      let pos' := clip (pos + vel') min_position max_position in
      (pos', vel')
    end.

Definition safe_env_body : StateT -> ActionT -> StateT :=
  fun state action =>
    let s' := unsafe_env_body state action in
    if Qle_bool (left_most s') (-1#1)
    then unsafe_env_body state Right
    else s'.

Definition unsafe_env : itree rlE unit := env_generator unsafe_env_body.
Definition safe_env : itree rlE unit := env_generator safe_env_body.

(* ref: https://github.com/openai/gym/blob/master/gym/envs/classic_control/mountain_car.py#L60 *)
Definition init_region (s: StateT) :=
  let (pos, vel) := s in
  pos <= -(2#5) /\ pos >= -(3#5) /\ vel = 0.

Definition bad_region (s: StateT) :=
  let (pos, vel) := s in
  pos <= -(1#1).

Definition trace_from_safe := fun tr => @trace_init StateT ActionT init_region tr.
Definition trace_fall := fun tr => @trace_end StateT ActionT bad_region tr.

Lemma inductive_invariant : forall s a s',
    left_most s > (-1#1) -> safe_env_body s a = s' -> left_most s' > (-1#1).
Proof.
Admitted.

Lemma left_most_to_pos : forall pos vel, left_most (pos, vel) >= (-1#1) -> pos >= (-1#1).
Proof.
  intros. unfold left_most in H.
  destruct (Qle_bool vel 0).
  - assert (pos - vel * vel / (2 # 1) / max_acc <= pos).
    + rewrite Qle_minus_iff. admit.
    + eapply Qle_trans; eauto.
  - auto.
Admitted.

Lemma safe: forall (tr: @trace rlE unit),
    @state_trace StateT actionE tr ->
    trace_from_safe tr ->
    trace_fall tr ->
    not (is_trace safe_env tr).
Proof.
Admitted.
