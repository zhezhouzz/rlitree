From Coq Require Import
     Morphisms
     Setoid
     RelationClasses
     Arith
     Lia
     List.

From ExtLib Require Import
     Monad
     Traversable
     Data.List.

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

(* There are only three effects. Read current state, read the action generated by agent with current state, update current state. Each step an agent goes in an environment will cause these three effects. *)

Inductive rlE : Type -> Type :=
| InputA : rlE ActionT
| InputS: rlE StateT
| OutputS : StateT -> rlE unit.

(* An enviornment has type "itree rlE unit", which says it can cause all effects in rlE and return nothing(the only output of an environment is exported by "OutputS"). It should first read current state and the action maked by agent, then write a new state. *)

Definition trigger_inr1 {D E : Type -> Type} : E ~> itree (D +' E)
  := fun _ e => ITree.trigger (inr1 e).
Arguments trigger_inr1 {D E} [T].

Definition unsafe_env : itree rlE unit :=
  (rec-fix env_ _ :=
     state <- trigger_inr1 InputS ;; (* read current state *)
           action <- ITree.trigger (inr1 InputA) ;; (* read action from agent *)
           match (state, action) with
           | (0, Left) => ITree.trigger (inr1 (OutputS 0)) ;; env_ tt
           | (S s, Left) => ITree.trigger (inr1 (OutputS s)) ;; env_ tt
           | (s, Right) => ITree.trigger (inr1 (OutputS (S s))) ;; env_ tt
           end
  ) tt.

Definition safe_env_body : StateT -> ActionT -> StateT :=
  fun state action =>
    match state with
    | 0 =>
      match action with
      | Left => 0
      | Right => S state
      end
    | S (2 as s) =>
      match action with
      | Left => 2
      | Right => 3
      end
    | S s =>
      match action with
      | Left => s
      | Right => S state
      end
    end.

(* A trace of a reinforcement environment looks like "{s <- InputS ;; a <- InputA ;; tt <- OutputS s'}*": "s" represents the current state, "a" represents the action generated by the agent, "s'" indicates the next state, which is the output of an environment. A RL trace has to follow the consistency requirement: the adjacent "s'" and "s" should be equal. i.e. in "s1 <- InputS ;; a1 <- InputA ;; tt <- OutputS s1' ;; a2 <- InputS ;; a2 <- InputA ;; tt <- OutputS s2'...", "s1' = s2".  *)

Notation "[ e , a ] t" := (TEventResponse e a t) (at level 80, right associativity).
Notation "[< e >]" := (TEventEnd e) (at level 80, right associativity).

Definition StepRecord : Type := StateT * ActionT * StateT.

Definition ret_rl_trace (x : StepRecord) : @trace rlE unit :=
  match x with
    (s, a, s') => [InputS, s] [InputA, a] [< OutputS s'>]
  end.
Definition bind_rl_trace (x : StepRecord) (tr: @trace rlE unit) : @trace rlE unit := 
  match x with
    (s, a, s') => [InputS, s] [InputA, a] [OutputS s', tt] tr
  end.

Definition step_adjacent (x1 x2: StepRecord) : Prop :=
  match x1, x2 with
    (s1, a1, s1'), (s2, a2, s2') => s1' = s2
  end.

Inductive is_rltrace : @trace rlE unit -> Prop :=
| ret_is_rltrace : forall x, is_rltrace (ret_rl_trace x)
| bind_ret_is_rltrace: forall x1 x2,
    step_adjacent x1 x2 ->
    is_rltrace (bind_rl_trace x1 (ret_rl_trace x2))
| bind_bind_is_rltrace: forall x1 x2 tr,
    step_adjacent x1 x2 ->
    is_rltrace (bind_rl_trace x2 tr) ->
    is_rltrace (bind_rl_trace x1 (bind_rl_trace x2 tr)).

(* An inductive invariant of an environment says: within one step "(s,a,s')", if "s" <= 3, forall "a", "s'" <=3. *)

Print Eqdep.EqdepTheory.inj_pair2.

Ltac inj_event_pair :=
  match goal with
  | [H : existT _ _ _ = existT _ _ _ |- _] => (apply (Eqdep.EqdepTheory.inj_pair2 Type) in H; subst)
  end.

Ltac clear_id :=
  match goal with
  | [H : ?a = ?a |- _] => clear H
  end.

Section Proper.
  Local Open Scope signature_scope.

  Global Instance proper_is_trace {E R} : Proper ((@eutt E R R eq) ==> eq ==> iff) is_trace.
  Proof.
    intros t t' Ht tr tr' Htr. subst tr'.
    apply trace_eq_iff_eutt in Ht.
    unfold trace_eq in Ht.
    intuition.
  Qed.

End Proper.

Ltac inj_event_pair_all := repeat (try inj_event_pair; idtac).
Ltac auto_is_trace_H H := unfold observe in H; cbn in H.
Ltac inv_is_trace H := auto_is_trace_H H; inversion H; try inj_event_pair_all; try clear_id; try clear H.

Lemma inv_vis_inputS : forall k s (tr: @trace rlE unit), is_trace (Vis InputS k) ([InputS, s] tr) -> is_trace (k s) tr.
Proof. intros. inv_is_trace H. auto. Qed.

Lemma inv_vis_inputA : forall k a (tr: @trace rlE unit), is_trace (Vis InputA k) ([InputA, a] tr) -> is_trace (k a) tr.
Proof. intros. inv_is_trace H. auto. Qed.

Lemma inv_vis_outputS : forall k s s' (tr: @trace rlE unit), is_trace (Vis (OutputS s) k) ([OutputS s', tt] tr) ->
                                                             s = s' ->
                                                             is_trace (k tt) tr.
Proof. intros. inv_is_trace H. auto. Qed.

Lemma inv_vis_outputS_2 : forall (k: unit -> itree rlE unit) s s' , is_trace (Vis (OutputS s) k) ([<OutputS s'>]) ->
                                                                    s = s'.
Proof. intros. inv_is_trace H. inversion H2. auto. Qed.

Lemma inv_vis_triggerS : forall k s (tr: @trace rlE unit), is_trace (ITree.bind (ITree.trigger InputS) k) ([InputS, s] tr) <-> is_trace (k s) tr.
Proof.
  split; intros.
  - repeat setoid_rewrite bind_trigger in H. inv_is_trace H. auto.
  - unfold is_trace, observe. cbn. constructor. auto.
Qed.

Lemma inv_vis_triggerA : forall k a (tr: @trace rlE unit), is_trace (ITree.bind (ITree.trigger InputA) k) ([InputA, a] tr) <-> is_trace (k a) tr.
Proof.
  split; intros.
  - repeat setoid_rewrite bind_trigger in H. inv_is_trace H. auto.
  - unfold is_trace, observe. cbn. constructor. auto.
Qed.

Lemma inv_vis_triggerSoutputS : forall k s s' (tr: @trace rlE unit),
    is_trace (ITree.trigger (OutputS s);; k tt) ([OutputS s', tt] tr) <-> s = s' /\ is_trace (k tt) tr.
Proof.
  split; intros.
  - repeat setoid_rewrite bind_trigger in H. inv_is_trace H. split; auto. inversion H2; auto.
  - destruct H. unfold is_trace, observe. cbn. rewrite H. constructor. auto.
Qed.

Lemma inv_vis_triggerSoutputSEnd : forall (t : itree rlE unit) s s',
    is_trace (ITree.trigger (OutputS s);; t) ([<OutputS s'>]) <-> s = s'.
Proof.
  split; intros.
  - repeat setoid_rewrite bind_trigger in H. inv_is_trace H. inversion H2; auto.
  - destruct H. unfold is_trace, observe. cbn. constructor.
Qed.

Definition env_generator (f: StateT -> ActionT -> StateT) : itree rlE unit :=
  (rec-fix env_ _ :=
     state <- trigger_inr1 InputS ;; (* read current state *)
           action <- trigger_inr1 InputA ;; (* read action from agent *)
           trigger_inr1 (OutputS (f state action)) ;; (* write new state *)
           env_ tt
  ) tt.

Definition step_generator (f: StateT -> ActionT -> StateT) : itree rlE unit :=
  state <- ITree.trigger InputS ;; (* read current state *)
        action <- ITree.trigger InputA ;; (* read action from agent *)
        ITree.trigger (OutputS (f state action)) ;; (* write new state *)
        Ret tt.

Lemma is_trace_bodyf : forall (s s': StateT) (a: ActionT) bodyf,
    is_trace (step_generator bodyf) (ret_rl_trace (s, a, s')) <->
    bodyf s a = s'.
Proof.
  split; intros.
  - unfold step_generator in H. cbn in H.
    rewrite inv_vis_triggerS in H.
    rewrite inv_vis_triggerA in H.
    rewrite inv_vis_triggerSoutputSEnd in H.
    auto.
  - unfold step_generator. cbn.
    rewrite inv_vis_triggerS.
    rewrite inv_vis_triggerA.
    rewrite inv_vis_triggerSoutputSEnd.
    auto.
Qed.

Lemma is_trace_rec_nil : forall (s s': StateT) (a: ActionT) bodyf,
    is_trace (env_generator bodyf) (ret_rl_trace (s, a, s')) <->
    is_trace (step_generator bodyf) (ret_rl_trace (s, a, s')).
Proof.
  split; intros.
  - setoid_rewrite rec_as_interp in H.
    match goal with
    | H: context [recursive ?b] |- _ => remember b as body in H
    end.
    repeat setoid_rewrite interp_bind in H.
    repeat setoid_rewrite interp_trigger in H.
    cbn in H.
    rewrite inv_vis_triggerS in H.
    rewrite inv_vis_triggerA in H.
    rewrite inv_vis_triggerSoutputSEnd in H.
    rewrite is_trace_bodyf. auto.
  - rewrite is_trace_bodyf in H.
    unfold env_generator. cbn.
    setoid_rewrite rec_as_interp.
    match goal with
    | H: _ |- context [recursive ?b] => remember b as body in H
    end.
    repeat setoid_rewrite interp_bind.
    repeat setoid_rewrite interp_trigger.
    cbn.
    rewrite inv_vis_triggerS.
    rewrite inv_vis_triggerA.
    rewrite inv_vis_triggerSoutputSEnd.
    auto.
Qed.

Definition safe_env : itree rlE unit := env_generator safe_env_body.

Lemma safe_inductive_invariant : forall (s s': StateT) (a: ActionT),
    safe_env_body s a = s' -> s <= 3 -> s' <= 3.
Proof.
  unfold safe_env_body.
  intros.
  repeat match goal with
         | H : context [match s with _ => _ end] |- _ => destruct s
         | H : context [match a with _ => _ end] |- _ => destruct a
         | _ => subst; auto; lia
         end.
Qed.

Lemma is_trace_rl_split: forall s a s' tr bodyf,
    is_trace (env_generator bodyf) (bind_rl_trace (s, a, s') tr) ->
    (is_trace (env_generator bodyf) tr) /\
    is_trace (env_generator bodyf) (ret_rl_trace (s, a, s')).
Proof.
  intros. cbn in H. unfold env_generator in H.
  setoid_rewrite rec_as_interp in H.
  match goal with
  | H: context [recursive ?b] |- _ => remember b as body in H
  end.
  repeat setoid_rewrite interp_bind in H.
  repeat setoid_rewrite interp_trigger in H.
  cbn in H.
  rewrite inv_vis_triggerS in H.
  rewrite inv_vis_triggerA in H.
  rewrite inv_vis_triggerSoutputS in H.
  destruct H. split.
  - unfold safe_env. unfold env_generator.
    unfold rec_fix.
    rewrite <- Heqbody.
    auto.
  - unfold safe_env.
    rewrite is_trace_rec_nil.
    rewrite is_trace_bodyf.
    auto.
Qed.

(* We can say, if an agent start form position less equal than 3, and the environment satisfies the inductive invariant, the trace of environment will not reach the position 4. *)

Inductive trace_init : (StateT -> Prop) -> @trace rlE unit -> Prop :=
| ret_trace_init :
    forall (s s': StateT) (a: ActionT) (phi: StateT -> Prop),
      phi s -> trace_init phi (ret_rl_trace (s, a, s'))
| bind_trace_init :
    forall (s s': StateT) (a: ActionT) (phi: StateT -> Prop) tr,
      phi s -> trace_init phi (bind_rl_trace (s, a, s') tr).

Inductive trace_end : (StateT -> Prop) -> @trace rlE unit -> Prop :=
| ret_trace_end :
    forall (s s': StateT) (a: ActionT) (phi: StateT -> Prop),
      phi s' -> trace_end phi (ret_rl_trace (s, a, s'))
| bind_trace_end :
    forall (s s': StateT) (a: ActionT) (phi: StateT -> Prop) tr,
      trace_end phi tr -> trace_end phi (bind_rl_trace (s, a, s') tr).

Lemma inv_trace_init_ret : forall phi s a s',
    trace_init phi (ret_rl_trace (s, a, s')) <-> phi s.
Proof.
  split; intros.
  - inv_is_trace H. auto.
  - constructor. auto.
Qed.

Lemma inv_trace_end_ret : forall phi s a s',
    trace_end phi (ret_rl_trace (s, a, s')) <-> phi s'.
Proof.
  split; intros.
  - inv_is_trace H. auto.
  - constructor. auto.
Qed.

Lemma inv_trace_init_bind : forall phi s a s' tr,
    trace_init phi (bind_rl_trace (s, a, s') tr) <->
    phi s.
Proof.
  split; intros.
  - inv_is_trace H. auto.
  - constructor. auto.
Qed.

Lemma inv_trace_end_bind : forall phi s a s' tr,
    trace_end phi (bind_rl_trace (s, a, s') tr) <->
    trace_end phi tr.
Proof.
  split; intros.
  - inv_is_trace H. auto.
  - constructor. auto.
Qed.

(* The following safe lemma can be proved by the inductive invariant. *)

Lemma safe: forall (tr: @trace rlE unit),
    is_rltrace tr ->
    trace_init (fun s => s <= 3) tr ->
    trace_end (fun s' => s' = 4) tr ->
    not (is_trace safe_env tr).
Proof.
  unfold not.
  intros. cbn in H0. unfold safe_env in H2.
  induction H.
  - destruct x, p.
    rewrite is_trace_rec_nil in H2.
    rewrite is_trace_bodyf in H2.
    rewrite inv_trace_init_ret in H0.
    rewrite inv_trace_end_ret in H1.
    apply safe_inductive_invariant in H2; auto.
    subst. lia.
  - destruct x1, x2, p, p0.
    rewrite inv_trace_init_bind in H0.
    rewrite inv_trace_end_bind in H1.
    rewrite inv_trace_end_ret in H1.
    inversion H. clear H.
    apply is_trace_rl_split in H2.
    destruct H2.
    rewrite is_trace_rec_nil in H.
    rewrite is_trace_rec_nil in H2.
    rewrite is_trace_bodyf in H.
    rewrite is_trace_bodyf in H2.
    apply safe_inductive_invariant in H2; auto. subst.
    apply safe_inductive_invariant in H; auto. lia.
  - destruct x1, x2, p, p0.
    rewrite inv_trace_init_bind in H0.
    rewrite inv_trace_end_bind in H1.
    rewrite inv_trace_end_bind in H1.
    inversion H. clear H. subst.
    apply is_trace_rl_split in H2.
    rewrite is_trace_rec_nil in H2.
    rewrite is_trace_bodyf in H2.
    destruct H2.
    apply IHis_rltrace; clear IHis_rltrace; auto.
    * rewrite inv_trace_init_bind. apply safe_inductive_invariant in H2; auto.
    * rewrite inv_trace_end_bind. auto.
Qed.
