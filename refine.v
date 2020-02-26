From RL Require Export TraceThm.

From Coq Require Import
     QArith
     Psatz
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

Definition EnvF A B := (A -> B -> A).

Definition inductive_invariant {S A: Type} (phi: S -> Prop) (env: EnvF S A) :=
  forall (s: S) (a: A) (s': S), phi s -> env s a = s' -> phi s'.

Definition safe {S A: Type} (env: itree rlE unit) (init: S -> Prop) (phi: S -> Prop):= forall (tr: @trace rlE unit),
    @state_trace S actionE tr ->
    @trace_init S A init tr ->
    @trace_end S A phi tr ->
    not (is_trace env tr).

Inductive safety_package {S A: Type} : (EnvF S A) -> (S -> Prop) -> (S -> Prop) -> (S -> Prop) -> Prop :=
| SafetyPackage: forall (envf:EnvF S A) (init phi iv: S -> Prop),
    inductive_invariant iv envf ->
    (forall s: S, (init s -> iv s) /\ (iv s -> not (phi s))) ->
    safety_package envf init phi iv.

Definition auto_safety_proof {S A: Type} (envf: EnvF S A) (init: S -> Prop) (phi: S -> Prop) (iv: S -> Prop):
           safety_package envf init phi iv -> safe (env_generator envf) init phi.
Proof. Admitted.

(* Mountain Car *)

Definition StateT := prod Q Q.

Inductive ActionT : Type :=
| Left
| Right.

Definition force := 1#1000.
Definition gravity := 3#1000.

(* approximate cos in Q *)
Definition cos (x: Q) :=
  1 - (x^2)/(2#1) + (x^4)/(24#1) - (x^6)/(720#1).

(* ref: https://github.com/openai/gym/blob/master/gym/envs/classic_control/mountain_car.py#L44 *)
Definition mountaincar_env_body : EnvF StateT ActionT :=
  fun state action =>
    let acc :=
        match action with
        | Left => - force
        | Right => force
        end in
    match state with
    | (pos, vel) =>
      let acc' := acc + cos((3#1) * pos) * (-gravity) in
      let vel' := vel + acc' in
      let pos' := pos + vel' in
      (pos', vel')
    end.

Definition mountaincar_env : itree rlE unit := env_generator mountaincar_env_body.

Definition mc_phi (s: StateT) :=
  let (pos, vel) := s in pos <= -(1#1).

Definition mc_init (s: StateT) :=
  let (pos, vel) := s in pos >= -(3#5) /\ pos <= -(2#5) /\ vel = 0.

Definition mc_potential (s: StateT) : Q:=
  let (pos, vel) := s in
  if Qle_bool vel 0
  then pos - (vel * vel) / (2#1) / (force + gravity)
  else pos.

Definition mc_iv := fun s => mc_potential s > -1#1.

Lemma mc_inductive_invariant : inductive_invariant mc_iv mountaincar_env_body.
Proof.
Admitted.

Lemma mc_P1: forall s, (mc_init s -> mc_iv s) /\ (mc_iv s -> not (mc_phi s)).
Proof.
  unfold mc_init, mc_iv, mc_potential, mc_phi. intros. destruct s. split.
  - intros. destruct H. destruct H0. subst. cbn. unfold force. unfold gravity. admit.
  - intros. admit.
Admitted.

Definition mc_safe: safety_package mountaincar_env_body mc_init mc_phi mc_iv.
Proof.
  constructor.
  apply mc_inductive_invariant. apply mc_P1.
Qed.
(* road *)

Definition StateT1 := prod Q Q.

Inductive ActionT1 : Type :=
| Forward
| NoAction
| Backward.

Definition road_init (s: StateT1) :=
  let (pos, vel) := s in pos <= -(2#5) /\ pos >= -(3#5) /\ vel = 0.

Definition road_phi (s: StateT1) :=
  let (pos, vel) := s in pos <= -(1#1).

Definition road_env_body : EnvF StateT1 ActionT1 :=
  fun state action =>
    let acc :=
        match action with
        | Forward => - force
        | NoAction => 0
        | Backward => force
        end in
    match state with
    | (pos, vel) =>
      let vel' := vel + acc in
      let pos' := pos + vel' in
      (pos', vel')
    end.

Definition road_env : itree rlE unit := env_generator road_env_body.

Definition road_potential (s: StateT1) : Q:=
  match s with
  | (pos, vel) => if Qle_bool vel 0 then pos - (vel * vel) / (2#1) / force else pos
  end.

Definition road_iv (s: StateT1) := road_potential s > -1#1.

Lemma road_inductive_invariant : inductive_invariant road_iv road_env_body.
Proof.
Admitted.

Lemma road_P1: forall s, (road_init s -> road_iv s) /\ (road_iv s -> not (road_phi s)).
Proof.
  unfold road_init, road_iv, road_potential, road_phi. intros. destruct s. split.
  - intros. destruct H. destruct H0.
Admitted.

Definition road_safe: safety_package road_env_body road_init road_phi road_iv.
Proof.
  constructor.
  apply road_inductive_invariant. apply road_P1.
Qed.

(* Two Dimension Road *)

Definition StateT2 := prod (prod Q Q) (prod Q Q).

Inductive ActionT2 : Type :=
| GoLeft
| GoRight
| GoForward
| GoBackward.

Definition twoDroad_env_body : EnvF StateT2 ActionT2 :=
  fun state action =>
    let (acc1, acc2) :=
        match action with
        | GoLeft => (0, -force)
        | GoRight => (0, force)
        | GoForward => (force, 0)
        | GoBackward => (-force, 0)
        end in
    match state with
      | ((pos1, vel1), (pos2, vel2)) =>
      let vel1' := vel1 + acc1 in
      let pos1' := pos1 + vel1' in
      let vel2' := vel2 + acc2 in
      let pos2' := pos2 + vel2' in
       ((pos1', vel1'), (pos2', vel2'))
    end.

Definition twoDroad_env : itree rlE unit := env_generator twoDroad_env_body.

Definition twoDroad_init (s: StateT2) :=
  match s with
  | (_, (pos2, vel2)) => pos2 <= -(2#5) /\ pos2 >= -(3#5) /\ vel2 = 0
  end.

Definition twoDroad_phi (s: StateT2) :=
  match s with
  | (_, (pos2, vel2)) => pos2 > -(1#1)
  end.

Definition twoDroad_iv (s: StateT2) :=
  match s with
  | (_, s) => road_potential s > -1#1
  end.

Definition twoDroad_safe: safe twoDroad_env twoDroad_init twoDroad_phi.
Proof. Admitted.

(* Refine relatoin *)

Definition state_map (s: StateT) : StateT1 :=
  let (pos, vel) := s in (pos, (1#2)*vel).

Definition action_map (a : ActionT) : ActionT1 :=
  match a with
  | Left => Forward
  | Right => Backward
  end.

(* Definition trace_map {S1 S2 A1 A2 R: Type} (smap: S1 -> S2) (amap: A1 -> A2) (tr: @trace (@rlE S1 A1) R): @trace (@rlE S2 A2) R := *)
(*   (fix _map (tr: @trace (@rlE S1 A1) R) : @trace (@rlE S2 A2) R := *)
(*   match tr with *)
(*   | TEnd => TEnd *)
(*   | TRet r => TRet r *)
(*   | @TEventEnd _ _ X e => *)
(*     (match e with *)
(*      | inl1 GetState => TEventEnd (inl1 GetState) *)
(*      | inl1 (PutState s) => TEventEnd (inl1 (PutState (smap s))) *)
(*      | inr1 AgentAction => TEventEnd (inr1 AgentAction) *)
(*      end) *)
(*   | @TEventResponse _ _ X e x tr => *)
(*     (match e with *)
(*      | inl1 GetState => TEventResponse (inl1 GetState) (smap x) (_map tr) *)
(*      | inl1 (PutState s) => TEventResponse (inl1 (PutState (smap s))) x (_map tr) *)
(*      | inr1 AgentAction => TEventResponse (inr1 AgentAction) (amap x) (_map tr) *)
(*      end) *)
(*   end) tr. *)

(* Map any traces from env1 to the trace from env2. Then if env2 safe, it will implies env1 safe. *)

Definition env_refine {S1 S2 A1 A2: Type}
           (env1: itree rlE unit) (env2: itree rlE unit)
           (init1: S1 -> Prop) (init2: S2 -> Prop)
           (phi1: S1 -> Prop) (phi2: S2 -> Prop) :=
  @safe S2 A2 env2 init2 phi2 -> @safe S1 A1 env1 init1 phi1.

Definition package_refine {S1 S2 A1 A2: Type}
           (env1: EnvF S1 A1) (env2: EnvF S2 A2)
           (init1: S1 -> Prop) (init2: S2 -> Prop)
           (phi1: S1 -> Prop) (phi2: S2 -> Prop)
           (iv1: S1 -> Prop) (iv2: S2 -> Prop):=
  @safety_package S2 A2 env2 init2 phi2 iv2 -> @safety_package S1 A1 env1 init1 phi1 iv1.

Definition envf_refine {S1 S2 A1 A2: Type}
           (smap: S1 -> S2) (amap: A1 -> A2)
           (env1: EnvF S1 A1) (env2: EnvF S2 A2)
           (init1: S1 -> Prop) (init2: S2 -> Prop)
           (phi1: S1 -> Prop) (phi2: S2 -> Prop)
           (iv1: S1 -> Prop) (iv2: S2 -> Prop) :=
  (forall s, (phi1 s -> phi2 (smap s)) /\ (init1 s -> init2 (smap s)) /\ (iv2 (smap s) <-> iv1 s)) /\
  (forall (s s': S1) (a: A1), ((iv2 (smap s) -> env2 (smap s) (amap a) = (smap s') -> iv2 (smap s')) ->
    (iv1 s -> env1 s a = s' -> iv1 s'))).

Lemma envf_refine_to_env_refine {S1 S2 A1 A2: Type} :
  forall (envf1: EnvF S1 A1) (envf2: EnvF S2 A2)
    (init1: S1 -> Prop) (init2: S2 -> Prop)
    (phi1: S1 -> Prop) (phi2: S2 -> Prop)
    (iv1: S1 -> Prop) (iv2: S2 -> Prop)
    (smap: S1 -> S2) (amap: A1 -> A2),
        envf_refine smap amap envf1 envf2 init1 init2 phi1 phi2 iv1 iv2 ->
    package_refine envf1 envf2 init1 init2 phi1 phi2 iv1 iv2.
Proof.
  intros.
  unfold package_refine. intros. 
  inversion H0; subst. clear H0.
  unfold envf_refine in H.
  destruct H.
  constructor.
  - unfold inductive_invariant. intros s a s'. apply H0. apply H1.
  - intros. remember (H2 (smap s)). clear H2 Heqa. destruct a. remember (H s). clear H Heqa.
    destruct a. destruct H4.
    split. 
    + intros. rewrite <- H5. auto.
    + unfold not. intros. apply H3. rewrite H5. auto. auto.
Qed.

Lemma envf_refine_example: envf_refine
                             state_map action_map
                             mountaincar_env_body road_env_body
                             mc_init road_init
                             mc_phi road_phi
                             mc_iv road_iv.
Proof.
  unfold envf_refine.
  split; intros.
  - split.
    + unfold mc_phi, road_phi, state_map. destruct s. nra.
    + split.
      * unfold mc_init, road_init, state_map. destruct s. intros. destruct H. destruct H0.
        split; auto. split; auto. subst. admit.
      * unfold road_iv, state_map, mc_iv. destruct s. unfold road_potential, mc_potential. remember (Qle_bool q0 0) as HB.
        destruct HB. assert (true = Qle_bool ((1 # 2) * q0) 0). admit. rewrite <- H. admit.
        assert (false = Qle_bool ((1 # 2) * q0) 0). admit. rewrite <- H. reflexivity.
  - destruct s, s'. unfold action_map; destruct a.
    unfold mc_init, road_init, state_map, action_map in H.
    unfold road_env_body in H.
    unfold mountaincar_env_body in H1.
    inversion H1. clear H1. subst.
    unfold road_iv, road_potential in H.
Admitted.

(* Bad refine relation *)

Definition state_map2 (s: StateT) : StateT2 := ((0, 0), s).

Definition action_map2 (a : ActionT) : ActionT2 :=
  match a with
  | Left => GoLeft
  | Right => GoRight
  end.

