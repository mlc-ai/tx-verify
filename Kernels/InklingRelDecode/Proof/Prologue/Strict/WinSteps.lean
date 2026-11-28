-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Window
import Kernels.InklingRelDecode.Proof.Common.StartupEvents
import Kernels.InklingRelDecode.Proof.Common.Staged.Early

@[expose] public section

/-! # The pieces of the strict window of the prologue

The first state of the thread, the invariant at it, and the strict step of every state of the
window (`OkG`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged PTX.Proof Control

noncomputable section

variable {Q : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem init_eq : (threadD Q L g).init = (.inl (Startup.init L g), fun _ => 0) := by
  show (Code.enter (Startup.code Q L g) (Code.withStubs (fragD Q L g) Startup.Entry.pc)
    (Code.gatedExit Startup.enterOf (sel L g)) (Startup.init L g), fun _ => (0 : Nat)) = _
  rw [Code.enter_none (Code.gatedExit_none.mpr enterOf_init)]

theorem win_step (hp : Pre Q L m) (hg : g < L.threads) (hlane : g % L.block < 128)
    (d : (threadD Q L g).D) (e : Event) (hd : OkG Q L g d) :
    (threadD Q L g).StepForQ (QT proQt) (WfG Q L g) d e := by
  rcases hd with ⟨s, n, rfl, -⟩ | ⟨d', n, rfl, hok⟩
  · intro t u ins hat hinv hc hq hw hf
    exact step_start hp hlane s n e hw ins hat hinv hc hq hw hf
  · exact step_pro hp hg d' n e hok

theorem win_init : OkG Q L g (threadD Q L g).init := by
  refine Or.inl ⟨Startup.init L g, fun _ => 0, init_eq, ?_⟩
  unfold Startup.init
  split <;> rfl

theorem win_q0 : ∀ t, (threadD Q L g).Good (some (threadD Q L g).init) t → QT proQt t := by
  intro t hgd
  rw [init_eq] at hgd
  refine qt_start (d := Startup.init L g) hgd.1 ?_
  unfold Startup.init
  split <;> (intro h; cases h)

end
end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
