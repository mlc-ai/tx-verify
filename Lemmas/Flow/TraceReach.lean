-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run

@[expose] public section

namespace PTX.Flow

/-- A nonterminal thread path records the events consumed between two exact states. -/
inductive TraceReach (K : Kernel) (A : List Assumption) (L : Launch) (g : Nat) :
    TState → List Event → TState → Prop
  | refl (t : TState) : TraceReach K A L g t [] t
  | tau {s u t : TState} {es : List Event} :
      Tau K A L g s u → TraceReach K A L g u es t → TraceReach K A L g s es t
  | event {s u t : TState} {es : List Event} {e : Event} :
      EStep K A L g s e (some u) →
        TraceReach K A L g u es t → TraceReach K A L g s (e :: es) t

namespace TraceReach

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

theorem append {s u t : TState} {es fs : List Event}
    (h : TraceReach K A L g s es u) (hn : TraceReach K A L g u fs t) :
    TraceReach K A L g s (es ++ fs) t := by
  induction h with
  | refl => exact hn
  | tau ht _ ih => exact .tau ht (ih hn)
  | event he _ ih => exact .event he (ih hn)

theorem of_local {s t : TState} (h : Relation.ReflTransGen (Tau K A L g) s t) :
    TraceReach K A L g s [] t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl _
  | head h _ ih => exact .tau h ih

end TraceReach
end PTX.Flow
