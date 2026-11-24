-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.Export
public import Kernels.TmlFa4Fwd.Proof.Lib.MemKind
public import Kernels.TmlFa4Fwd.Proof.Common.Open
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.ReadAddr
import Kernels.TmlFa4Fwd.Proof.Epilogue.Open
import Kernels.TmlFa4Fwd.Proof.Epilogue.Warp
import Kernels.TmlFa4Fwd.Proof.Startup.Export.Mem

@[expose] public section

/-! # The output warp's memory events

An event of the output warp that accesses memory is a read of a scheduler word or a tensor store
(`epi_mem`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **The output warp's memory events.** -/
theorem epi_mem (hw : Prologue.warpIndex L g = 13) {e : Event} (he : X.get (g, k) = some e)
    (hm : MemKind e.kind) :
    (∃ a bs, e.kind = .rd a bs ∧ InWord p a) ∨ ∃ a s, e.kind = .tensorStore a s := by
  have hub : ∀ f, e.kind ≠ .ub f := by intro f h; rw [h] at hm; exact hm
  rcases Epilogue.open_ev hp hX hFw hw he hub with ⟨s, n, -, -, -, hi, hev⟩ |
    ⟨d, n, hσ, h0, hR, hi, hev⟩
  · exact (start_mem hev hi.2 hm).elim
  have hF : Epilogue.Fits p L g d (n .shfl) (n .vote) := hR.1
  by_cases hr : ∃ a bs, e.kind = .rd a bs
  · obtain ⟨a, bs, hk⟩ := hr
    exact .inl ⟨a, bs, hk, Epilogue.sched_rd hp hF hev hk⟩
  right
  have hno : ∀ kd, e.kind = kd → ¬ MemKind kd → False := fun kd h h' => h' (h ▸ hm)
  cases hs : d.site <;> simp only [Epilogue.Ev, hs] at hev
  case word | q0 | q1 =>
    rcases hev with ⟨bs, hk⟩ | ⟨f, hk⟩
    · exact (hr ⟨_, _, hk⟩).elim
    · exact (hub f hk).elim
  case store =>
    unfold Epilogue.isStore at hev
    split at hev
    · rename_i a s hk; exact ⟨a, s, hk⟩
    · rename_i f hk; exact (hub f hk).elim
    · cases hev
  case start => obtain ⟨_, _, _, h⟩ := hev; exact (hno _ h id).elim
  case ready => obtain ⟨_, h⟩ := hev; exact (hno _ h id).elim
  case vote => obtain ⟨_, h⟩ := hev; exact (hno _ h id).elim
  case down | up | total | pre | tiles => obtain ⟨_, _, h⟩ := hev; exact (hno _ h id).elim
  all_goals exact (hno _ hev id).elim

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
