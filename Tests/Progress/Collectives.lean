-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Reg
public import Lemmas.Kernel.Progress.TcColl
public import Lemmas.Kernel.Progress.BarGroup

/-! # Progress at the collectives, for a kernel of 512-thread blocks

The collective templates promoted from FA4 composed into one dispatcher: a blocked pending
thread at a register request, a warp-collective `tcgen05` event, a `bar.sync` or an unrecorded
`bar.arrive` steps, from the safety goal, the kernel's matching facts and its time table's facts
(tml-fa4's and FA4's blocks are 512 threads, so `warp_mate` applies). -/

namespace PTX.Tests.Collectives
open PTX PTX.Sched

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {M : Timed K A L}
  {X : Execution}

example (hblock : L.block = 512) (hwf : Assumption.WfStep (fun _ => true) L K mem0 A)
    (hC : ∀ g < L.threads, (M.code g).Sound) (hs : SafeGoal K A L mem0)
    (hmatch : RegMatch L X) (hexit : RegExit L X) {T : Nat}
    (hbefore : ∀ {h : Nat}, h < L.threads →
      (∀ j pc inc n inst, X.get (h, j) ≠ some ⟨pc, .setMaxReg inc n inst⟩) →
      threadTime M X h ≤ T)
    (hafterR : ∀ {g k pc n inst : Nat} {inc : Bool}, g < L.threads →
      X.get (g, k) = some ⟨pc, .setMaxReg inc n inst⟩ →
      ∃ d, Frame.stateAt M.code X g (k + 1) = some (some d) ∧ T < M.time g d)
    (hlagT : ∀ {g h j k : Nat} {d : (M.code g).D}, g < L.threads → h < L.threads →
      SameWarp L g h → X.TcK (g, j) k → Frame.stateAt M.code X g j = some (some d) →
      (X.tr h).countP isTcColl ≤ k → threadTime M X h ≤ M.time g d)
    (hafterT : ∀ {g j k : Nat} {d : (M.code g).D}, g < L.threads → X.TcK (g, j) k →
      Frame.stateAt M.code X g j = some (some d) →
      (∃ d', Frame.stateAt M.code X g (j + 1) = some (some d') ∧ M.time g d < M.time g d') ∨
        Frame.stateAt M.code X g (j + 1) = none)
    {G : Nat → Nat → Prop}
    (hgroup : ∀ {g i pc id : Nat} {cnt : Option Nat} {m : BarMode}, g < L.threads →
      X.get (g, i) = some ⟨pc, .bar id cnt m⟩ →
      ∃ p : Finset Nat, NamedBar.Shape L cnt p id ∧ NamedBar.Sources L X cnt p id ∧
        ∀ w ∈ p, G id w)
    (hafterB : ∀ {g j pc id : Nat} {cnt : Option Nat} {m : BarMode} {d : (M.code g).D},
      g < L.threads → X.get (g, j) = some ⟨pc, .bar id cnt m⟩ →
      Frame.stateAt M.code X g j = some (some d) →
      (∃ d', Frame.stateAt M.code X g (j + 1) = some (some d') ∧ M.time g d < M.time g d') ∨
        Frame.stateAt M.code X g (j + 1) = none)
    (hlagS : ∀ {g y j pc id : Nat} {cnt : Option Nat} {d : (M.code g).D},
      g < L.threads → y < L.threads → y / L.block = g / L.block → G id (y % L.block / 32) →
      X.get (g, j) = some ⟨pc, .bar id cnt .sync⟩ → Frame.stateAt M.code X g j = some (some d) →
      (X.tr y).countP (Execution.isBarId id) ≤ ((X.tr g).take j).countP (Execution.isBarId id) →
        (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧ threadTime M X y ≤ M.time g d)
    (hlagW : ∀ {g y j pc id : Nat} {cnt : Option Nat} {m : BarMode} {d : (M.code g).D},
      g < L.threads → y < L.threads → SameWarp L g y →
      X.get (g, j) = some ⟨pc, .bar id cnt m⟩ → Frame.stateAt M.code X g j = some (some d) →
      (X.tr y).countP (Execution.isBarId id) ≤ ((X.tr g).take j).countP (Execution.isBarId id) →
        (∀ k pc', X.get (y, k) ≠ some ⟨pc', .exit⟩) ∧ threadTime M X y ≤ M.time g d)
    (htr : Frame.Tracked M.code X) (hmax : Maximal L K A mem0 X) {g : Nat}
    (hp : Frame.Pending L X g) (hrel : ¬ Step.Released L X g)
    (hk : RegWait L X g ∨ TcWait L X g ∨ BarWait L X g ∨ ArriveWait L X g) :
    Steps M mem0 X (.thread g) := by
  rcases hk with h | h | h | h
  · exact reg_steps hs hmatch hexit (by rw [hblock]) hbefore hafterR hmax hp hrel h
  · exact tc_steps hC hs htr hlagT hafterT hmax hp hrel h
  · exact barGroup_sync_steps hwf hC hs hgroup hafterB hlagS htr hmax hp hrel h
  · exact barGroup_arrive_steps hwf hC hs hgroup hafterB hlagW htr hmax hp hrel h

end PTX.Tests.Collectives
