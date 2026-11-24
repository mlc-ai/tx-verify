-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Lemmas.Flow.TraceInduction
public import Lemmas.Kernel.Frame

@[expose] public section

/-! # The composed machine dispatches each role to its launch warp -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.RingRoleGeometry

open PTX PTX.Flow

/-- The thread geometry of each followed body state. -/
def valid (L : Launch) (g : Nat) : Option Machine.ThreadD → Prop
  | some (.wg0 _) => wgOf L g = 0
  | some (.wg2 _) => wgOf L g = 2
  | some (.mma _) => warpOf L g = 4
  | some (.tma _) => warpOf L g = 5
  | some (.index _) => warpOf L g = 7
  | _ => True

private theorem next_valid {P : Params} {L : Launch} {g : Nat} {e : Event}
    {d d' : Option Machine.ThreadD} (hv : valid L g d)
    (hn : (Machine.machine P L g).next d e = some d') : valid L g d' := by
  cases d
  case none =>
    change some none = some d' at hn
    cases hn
    trivial
  case some d =>
    change Machine.next P L g d e = some d' at hn
    cases d
    case prologue s =>
      simp only [Machine.next] at hn
      split at hn
      · cases hn
        trivial
      · split at hn
        · rename_i w _
          split_ifs at hn with hg
          · fin_cases w <;> cases hn <;> first | exact hg | trivial
          · cases hn
            trivial
        · cases hn
          trivial
      · cases hn
    case head =>
      cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
      simp only [Machine.headStart] at hn
      split_ifs at hn <;> cases hn <;> assumption
    all_goals
      simp only [Machine.next] at hn
      all_goals repeat' split at hn
      all_goals cases hn
      all_goals first | exact hv | trivial

/-- An actual followed body state has its role's CTA-local warp or warpgroup. -/
theorem of_trace {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat} {d : Machine.ThreadD}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
    (hs : (Machine.machine P L g).Sound)
    (hst : Frame.stateAt (Machine.code P L) X g i = some (some d)) :
    valid L g (some d) :=
  (hs.produces (hX.thr g hg)).prefix_induction (fun q _ => valid L g q)
    trivial (fun _ _ _ _ _ h _ hn => next_valid h hn) i (some d) hst

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.RingRoleGeometry
