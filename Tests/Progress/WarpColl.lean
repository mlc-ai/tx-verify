-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.WarpColl

/-! # A released lane at a warp collective, in a kernel without cancellation

`Sched.warpColl_steps` with the next-event classification `AtColl`, for a kernel of 512-thread
blocks that issues no cancellation request (every thread launched, none canceled): the warp's
key is the thread's CTA and warp, which lanes of one warp share. -/

namespace PTX.Tests.WarpColl
open PTX PTX.Sched

example {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
    {X : Execution} (hblock : L.block = 512)
    (hK : K.code.all (fun ins => !voteModeOp ins.op) = true)
    (hsound : ∀ g < L.threads, (M.code g).Sound) (hs : SafeGoal K A L mem0)
    (htr : Frame.Tracked M.code X) {AtColl : ∀ g, (M.code g).D → Prop}
    (hw : WarpCollFacts M X (fun g => (g / L.block, g % L.block / 32)) AtColl)
    (hlaunch : ∀ h, Step.Launched L X h) (hcl : ∀ h, ¬ ClcCanceled L X h)
    (happ : ∀ (ds : List Nat) (ev : Nat → Event), (∀ x, (ev x).kind.readsMem = false) →
      ∀ a ∈ A, a.wf L mem0 (X.appendLanes ds ev))
    (hubx : ∀ {h : Nat} {t t1 : TState} {f : Fault}, h < L.threads → Step.Released L X h →
      Run K A L h {} (X.tr h) (some t) → Relation.ReflTransGen (Tau K A L h) t t1 →
      out K A L h t1 = .ev (.ub f) → ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L)
    (hmax : Maximal L K A mem0 X) {g : Nat} (hp : Frame.Pending L X g) {d : (M.code g).D}
    (hσ : Frame.stateAt M.code X g (X.tr g).length = some (some d)) (hk : AtColl g d)
    (hrel : Step.Released L X g) : Steps M mem0 X (.thread g) :=
  warpColl_steps hK (fun hsw => by rw [hsw.1.2.2, hsw.2]) hsound hs htr hw (by rw [hblock])
    hlaunch hcl happ hubx hmax hp hσ hk hrel

end PTX.Tests.WarpColl
