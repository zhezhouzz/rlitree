From Coq Require Import
     Wellfounded
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
Import SumNotations.
Open Scope monad_scope.

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

(* inj_pair2_dec *)

Ltac inj_dep_pair :=
  match goal with
  | [H : existT _ _ _ = existT _ _ _ |- _] => (apply (Eqdep.EqdepTheory.inj_pair2 Type) in H; subst)
  end.

Ltac clear_id :=
  match goal with
  | [H : ?a = ?a |- _] => clear H
  end.

Ltac inj_dep_pair_all := repeat (try inj_dep_pair; idtac).
Ltac auto_is_trace_H H := unfold observe in H; cbn in H.
Ltac inv_is_trace H := auto_is_trace_H H; inversion H; try inj_dep_pair_all; try clear_id; try clear H.

Ltac inv_dep H := inversion H; subst; try inj_dep_pair_all; try clear_id; try clear H.


(* There are only three effects. Read current state, read the action generated by agent with current state, update current state. Each step an agent goes in an environment will cause these three effects. *)

Inductive stateE {StateT : Type}: Type -> Type :=
| GetState: stateE StateT
| PutState : StateT -> stateE unit.

Inductive actionE {ActionT : Type}: Type -> Type :=
| AgentAction : actionE ActionT.

Definition rlE {StateT ActionT: Type} := (@stateE StateT) +' (@actionE ActionT).

(* A trace of a reinforcement environment looks like "{s <- GetState ;; a <- AgentAction ;; tt <- PutState s'}*": "s" represents the current state, "a" represents the action generated by the agent, "s'" indicates the next state, which is the output of an environment. A RL trace has to follow the consistency requirement: the adjacent "s'" and "s" should be equal. i.e. in "s1 <- GetState ;; a1 <- AgentAction ;; tt <- PutState s1' ;; a2 <- GetState ;; a2 <- AgentAction ;; tt <- PutState s2'...", "s1' = s2".  *)

Notation "[ e , a ] t" := (TEventResponse e a t) (at level 80, right associativity).
Notation "[< e >]" := (TEventEnd e) (at level 80, right associativity).
Open Scope sum_scope.

Inductive state_trace {StateT: Type} {E: Type -> Type}: @trace ((@stateE StateT) +' E) unit -> Prop :=
| Str00 : state_trace TEnd
| Str01 : forall {X} (e: ((@stateE StateT) +' E) X), state_trace ([< e >])
| Str10 : forall {X} (e: @stateE StateT X) r, state_trace ([(e|), r] TEnd)

| Str20 : forall {X} (e : E X) r tr, state_trace tr -> state_trace ([(|e), r] tr)
                                                                   
| Str21 : forall s1 s2 tr, state_trace ([ (GetState|), s2] tr) -> s1 = s2 ->
                           state_trace ([ (GetState|), s1] [ (GetState|), s2] tr)
| Str22 : forall s1 s2 tr, state_trace ([ (PutState s2|), tt] tr) ->
                           state_trace ([ (GetState|), s1] [ (PutState s2|), tt] tr)
| Str23 : forall {X} (e2: E X) s1 r2 tr,
    state_trace ([(GetState|), s1] tr) ->
    state_trace ([(GetState|), s1] [ (|e2), r2] tr)

| Str24 : forall s1 s2 tr, state_trace ([ (GetState|), s2] tr) -> s1 = s2 ->
                           state_trace ([ (PutState s1|), tt] [ (GetState|), s2] tr)
| Str25 : forall s1 s2 tr, state_trace ([ (PutState s2|), tt] tr) ->
                           state_trace ([ (PutState s1|), tt] [ (PutState s2|), tt] tr)
| Str26 : forall {X} (e2: E X) s1 r2 tr,
    state_trace ([(PutState s1|), tt] tr) ->
    state_trace ([(PutState s1|), tt] [ (|e2), r2] tr).

Hint Constructors state_trace.

Lemma decrease_state_trace_inr {StateT X: Type} {E: Type -> Type}: forall e (r:X) (tr: @trace ((@stateE StateT) +' E) unit),
    state_trace ([(|e), r] tr) <->
    state_trace tr.
Proof.
  split; intros.
  - inv_dep H; auto.
  - auto.
Qed.

Lemma decrease_state_trace_put {StateT: Type} {E: Type -> Type}: forall s (tr: @trace ((@stateE StateT) +' E) unit),
    state_trace ([(PutState s|), tt] tr) ->
    state_trace tr.
Proof.
  intros.
  induction tr; auto.
  - inv_dep H.
  - inv_dep H; auto.
Qed.

Lemma decrease_state_trace_get {StateT: Type} {E: Type -> Type}: forall s (tr: @trace ((@stateE StateT) +' E) unit),
    state_trace ([(GetState|), s] tr) ->
    state_trace tr.
Proof.
  intros.
  induction tr; auto.
  - inv_dep H.
  - inv_dep H; auto.
Qed.

Lemma decrease_state_trace {StateT X: Type} {E: Type -> Type}: forall e (r:X) (tr: @trace ((@stateE StateT) +' E) unit),
    state_trace ([e, r] tr) ->
    state_trace tr.
Proof.
  intros.
  destruct e.
  - inv_dep H; auto.
    + rewrite decrease_state_trace_inr.
      apply decrease_state_trace_get in H1; auto.
    + rewrite decrease_state_trace_inr.
      apply decrease_state_trace_put in H1; auto.
  - rewrite decrease_state_trace_inr in H. auto.
Qed.

(* Trace Length *)

Fixpoint trace_length {R: Type} {E: Type -> Type} (tr: @trace E R) : nat :=
  match tr with
  | TEnd => 0
  | TRet _ => 1
  | TEventEnd _ => 1
  | TEventResponse _ _ tr => S (trace_length tr)
  end.

(* inversion lemma for is_trace *)

Lemma inv_vis : forall (E : Type -> Type) (R T: Type) (k : T -> _) e1 e2 (s : T) (tr: @trace E R), is_trace (Vis e1 k) ([e2, s] tr) <-> e1 = e2 /\ is_trace (k s) tr.
Proof.
  split; intros.
  - inv_is_trace H. split; auto.
  - destruct H. rewrite H. constructor. unfold is_trace in H0. auto.
Qed.

Lemma inv_trigger_eres : forall (E : Type -> Type) (R T: Type), forall (k : T -> _) e1 e2 s (tr: @trace E R),
    is_trace (ITree.bind (ITree.trigger e1) k) ([e2, s] tr) <-> e1 = e2 /\ is_trace (k s) tr.
Proof.
  intros.
  repeat setoid_rewrite bind_trigger.
  rewrite inv_vis. split; auto.
Qed.

Lemma inv_trigger_eend {E : Type -> Type} {R T: Type}: forall (k : T -> _) (e1 e2: E T),
    @is_trace E R (ITree.bind (ITree.trigger e1) k) ([<e2>]) <-> e1 = e2.
Proof.
  split; intros.
  - repeat setoid_rewrite bind_trigger in H. inv_is_trace H. auto.
  - unfold is_trace, observe. cbn. destruct H. subst. constructor.
Qed.

Lemma inv_trigger_ret {E : Type -> Type} {R T: Type}: forall (k : T -> _) (e1 e2: E T) t,
    @is_trace E R (ITree.bind (ITree.trigger e1) k) (TRet t) -> False.
Proof.
  intros.
  - repeat setoid_rewrite bind_trigger in H. inv_is_trace H.
Qed.

Ltac inv_env :=
  match goal with
  | H : is_trace (ITree.bind (ITree.trigger _) _) ([_, _] _) |- _ =>
    rewrite inv_trigger_eres in H; destruct H; subst; auto
  | H : is_trace (ITree.bind (ITree.trigger _) _) ([<_>]) |- _ =>
    rewrite inv_trigger_eend in H; subst; auto
  | H : is_trace (ITree.bind (ITree.trigger _) _) (TRet _) |- _ =>
    apply inv_trigger_ret in H; auto
  end.

(* Environment *)

(* The rl environment to has to gerantee the following rule: *)
(*   1) read a state, i.e. "s". *)
(*   2) read a action from agent, i.e. "a". *)
(*   3) run a pure function "f: StateT -> ActionT -> StateT" on the read state and action, i.e. "s' <- f s a". *)
(*   4) rewrite the new state, i.e. "s'". *)
(*   5) go back to step 1. *)

(* be notation *)

Definition env_body {StateT ActionT : Type} (f: StateT -> ActionT -> StateT) : unit -> itree (callE unit unit +' rlE) unit :=
  (fun _ : unit =>
            state <- ITree.trigger (|GetState|);;
            action <- ITree.trigger (||AgentAction);;
            ITree.trigger (|PutState (f state action)|);; call tt).

Definition env_generator {StateT ActionT : Type} (f: StateT -> ActionT -> StateT) : itree (@rlE StateT ActionT) unit :=
  rec (env_body f) tt.

Inductive step_trace {StateT ActionT : Type} : (StateT -> ActionT -> StateT) -> @trace (@rlE StateT ActionT) unit -> Prop :=
| step_trace00 : forall f, step_trace f TEnd
| step_trace01 : forall f, step_trace f ([<(GetState|)>])
| step_trace10 : forall f s, step_trace f ([(GetState|), s] TEnd)
| step_trace11 : forall f s, step_trace f ([(GetState|), s] [<(| AgentAction)>])
| step_trace20 : forall f s a, step_trace f ([(GetState|), s] [(|AgentAction), a] TEnd)
| step_trace21 : forall f s a s',
    f s a = s' ->
    step_trace f ([(GetState|), s] [(|AgentAction), a] [<(PutState s'|)>])
| step_trace3: forall f s a s' tr t,
    step_trace f tr ->
    t = tt ->
    f s a = s' ->
    step_trace f ([(GetState|), s] [(|AgentAction), a] [(PutState s'|), t] tr).

Hint Constructors step_trace.

Lemma inv_step_trace {StateT ActionT : Type} : forall (f: StateT -> ActionT -> StateT) s a s' tr t,
    step_trace f ([(GetState|), s] [(|AgentAction), a] [(PutState s'|), t] tr) <->
    step_trace f tr /\ t = tt /\ f s a = s'.
Proof.
  split; intros.
  - inv_dep H. split; auto.
  - destruct H. destruct H0. auto.
Qed.

Ltac is_trace_autoinv :=
  repeat match goal with
         | H : is_trace _ (TEventEnd ?a) |- _ => cbn in H; try (rewrite inv_trigger_eend in H)
         | H : is_trace _ _ |- _ => cbn in H; try (rewrite inv_trigger_eres in H)
         | H : _ /\ _ |- _ => destruct H
         end.

Ltac is_trace_auto :=
  repeat match goal with
         | H : _ |- is_trace _ (TEventEnd ?a) => cbn; try (rewrite inv_trigger_eend)
         | H : _ |- is_trace _ _ => cbn; try (rewrite inv_trigger_eres)
         | H : _ |- _ /\ _ => split; subst; auto
         end.

Lemma unfold_one_env {StateT ActionT : Type} : forall (bodyf: StateT -> ActionT -> StateT),
    (rec (env_body bodyf) tt) ≈ (r <- ITree.trigger (GetState|);;
                                   r0 <- ITree.trigger (|AgentAction);;
                                   ITree.trigger (PutState (bodyf r r0)|);;
                                   (rec (env_body bodyf) tt)).
Proof.
  intros.
  setoid_rewrite rec_as_interp at 1.
  unfold env_body at 2.
  repeat setoid_rewrite interp_bind.
  repeat setoid_rewrite interp_trigger.
  cbn. reflexivity.
Qed.

Lemma env_trace_is_step_trace {StateT ActionT : Type} : forall tr bodyf, is_trace (env_generator bodyf) tr <-> @step_trace StateT ActionT bodyf tr.
Proof.
  unfold env_generator. split; intros.
  - induction tr using (well_founded_induction
                          (wf_inverse_image _ nat _ trace_length
                                            PeanoNat.Nat.lt_wf_0)).
    rewrite unfold_one_env in H.
    repeat setoid_rewrite bind_trigger in H.
    destruct tr; try inv_is_trace H; auto.
    destruct tr; try inv_is_trace H2; auto.
    destruct tr; try inv_is_trace H1; auto.
    constructor; auto.
    + apply H0. cbn. lia. auto.
    + destruct x1. auto.
  - rewrite unfold_one_env.
    repeat setoid_rewrite bind_trigger.
    induction H; try repeat constructor.
    + rewrite H. constructor.
    + rewrite H1. constructor.
      assert (is_trace (rec (env_body f) tt) tr).
      * setoid_rewrite unfold_one_env.
        repeat setoid_rewrite bind_trigger.
        auto.
      * unfold is_trace in H2. auto.
Qed.

(* The first input state of a trace satisfy the property phi. *)

Inductive trace_init {StateT ActionT: Type} : (StateT -> Prop) -> @trace (@rlE StateT ActionT) unit -> Prop :=
| head_trace_init : forall tr (phi: StateT -> Prop) s, phi s -> trace_init phi ([(GetState|), s] tr).

(* The last output state of a trace satisfy the property phi. *)

Inductive trace_end {StateT ActionT: Type} : (StateT -> Prop) -> @trace (@rlE StateT ActionT) unit -> Prop :=
| tail_trace_end :
    forall (s': StateT) (a: ActionT) (phi: StateT -> Prop),
      phi s' -> trace_end phi ([< (PutState s'|) >])
| cons_trace_end :
    forall {X} (s s': StateT) e (r:X) (phi: StateT -> Prop) tr,
      trace_end phi tr -> trace_end phi ([e, r] tr).

Hint Constructors trace_init.
Hint Constructors trace_end.

Ltac inv_trace_init :=
  repeat match goal with
           | H : trace_init _ (TEnd) |- _ => inversion H; subst; auto
           | H : trace_init _ ([_, _] _) |- _ => inv_is_trace H
           | H : trace_init _ ([<_>]) |- _ => inv_is_trace H; subst; auto
           end.

Ltac inv_trace_end :=
  repeat match goal with
           | H : trace_end _ (TEnd) |- _ => inversion H; subst; auto
           | H : trace_end _ ([_, _] _) |- _ => inv_is_trace H
           | H : trace_end _ ([<_>]) |- _ => inv_is_trace H; subst; auto
           end.