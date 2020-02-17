From RL Require Export TraceThm.

From Coq Require Import
     Arith
     Lia
     List.

From ITree Require Import
     ITree
     ITreeFacts
     Traces.

Import ListNotations.
Import ITreeNotations.
Import MonadNotation.
Open Scope monad_scope.

(* * Idea * *)
(* An environment is an transition system over state space and action space. An deterministic environment has type "State * Action -> State" and an agent policy has type "State -> Action". Now represent an environment as an itree and agent policy as effect. *)

(* * Example * *)
(* One-demension road with cliff. State space has type "nat" and there is a cliff at position "4". Action space is "{Left, Right}". If the car reach position "4" it will crash. A safe environment should not let this happen while any decision the agent makes. *)

Definition StateT := nat.

Inductive ActionT : Type :=
| Left
| Right.

(* An one-dimension road environment. Input action "Left" then go left, input action "Right" then go right.  *)

Definition unsafe_env_body : StateT -> ActionT -> StateT :=
  fun state action =>
    match action with
    | Left => state - 1
    | Right => state + 1
    end.

(* A safe environment adds a barrier at 3. *)

Definition safe_env_body : StateT -> ActionT -> StateT :=
  fun state action =>
    match action with
    | Left => state - 1
    | Right => if state =? 3 then 3 else state + 1
    end.

Definition unsafe_env : itree rlE unit := env_generator unsafe_env_body.
Definition safe_env : itree rlE unit := env_generator safe_env_body.

Lemma safe_inductive_invariant : forall (s s': StateT) (a: ActionT),
    safe_env_body s a = s' -> s <= 3 -> s' <= 3.
Proof.
  unfold safe_env_body.
  intros.
  repeat match goal with
         | H : context [if s =? _ then _ else _] |- _ => destruct s; cbn in H
         | H : context [match a with _ => _ end] |- _ => destruct a
         | _ => subst; auto; lia
         end.
Qed.

Definition trace_from_safe := fun tr => @trace_init StateT ActionT (fun s => s <= 3) tr.
Definition trace_fall := fun tr => @trace_end StateT ActionT (fun s' => s' = 4) tr.

(* The following safe lemma can be proved by the inductive invariant. *)

Lemma safe: forall (tr: @trace rlE unit),
    @state_trace StateT actionE tr ->
    trace_from_safe tr ->
    trace_fall tr ->
    not (is_trace safe_env tr).
Proof.
  unfold not, trace_from_safe, trace_fall.
  intros. unfold safe_env, env_generator in H2.
  apply env_trace_is_step_trace in H2.
  remember safe_env_body as z.
  induction H2; try inv_trace_end; try inv_trace_init.
  - apply safe_inductive_invariant in H4; auto. lia.
  - apply IHstep_trace; auto.
    + do 3 (apply decrease_state_trace in H). auto.
    + remember (safe_env_body s a) as z.
      assert (z <= 3).
      rewrite Heqz. apply safe_inductive_invariant with s a; auto.
      * do 2 (apply decrease_state_trace in H).
        inv_dep H; try inv_trace_end; auto.
        constructor; auto.
        inversion H2.
        inversion H2.
Qed.