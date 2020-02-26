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

Definition trace_map {S1 S2 A1 A2 R: Type} (smap: S1 -> S2) (amap: A1 -> A2) (tr: @trace (@rlE S1 A1) R): @trace (@rlE S2 A2) R :=
  (fix _map (tr: @trace (@rlE S1 A1) R) : @trace (@rlE S2 A2) R :=
  match tr with
  | TEnd => TEnd
  | TRet r => TRet r
  | @TEventEnd _ _ X e =>
    (match e with
     | inl1 GetState => TEventEnd (inl1 GetState)
     | inl1 (PutState s) => TEventEnd (inl1 (PutState (smap s)))
     | inr1 AgentAction => TEventEnd (inr1 AgentAction)
     end)
  | @TEventResponse _ _ X e x tr =>
    (match e with
     | inl1 GetState => TEventResponse (inl1 GetState) (smap x) (_map tr)
     | inl1 (PutState s) => TEventResponse (inl1 (PutState (smap s))) x (_map tr)
     | inr1 AgentAction => TEventResponse (inr1 AgentAction) (amap x) (_map tr)
     end)
  end) tr.
