-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.BarRows
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.TmemRows
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part056

@[expose] public section

/-! # The dispatch's row: where an mbarrier event is

`mbarRow_place`: under `Follow`, an event of a launched lane that names an mbarrier is at a pc of
the code of the role whose lane condition the lane meets (`MbarRow.Place`). The state behind the
event is at the event's pc and in its role's code (`place_state`, `Common/Where.lean`), or at the
final `ret`, whose event is `exit` and names no mbarrier. `barRow_place`: the same for a
named-barrier event (`BarRow.Place`), `tmemRow_place` for a `tcgen05` event (`TmemRow.Place`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- An event of a launched lane, neither undefined behaviour nor `exit`, is at a pc of the code of
the role whose lane condition the lane meets. -/
private theorem event_place (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hub : ∀ f, e.kind ≠ .ub f) (hne : e.kind ≠ .exit) :
    StartupAt e.pc ∨ Wg0At L g e.pc ∨ Wg1At L g e.pc ∨ MmaAt L g e.pc ∨ TmaAt L g e.pc ∨
      IndexAt L g e.pc ∨ DequantAt L g e.pc := by
  obtain ⟨σ, hσ, hJ, hi, -, hpc⟩ := ev_at hp hX hFw he hub
  rw [hpc]
  rcases place_state hp hJ hi with h | h | h | h | h | h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inr (.inr (.inl h))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl h)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr h)))))
  · exfalso
    obtain ⟨t, ins, o, -, -, hc, hf⟩ :=
      Frame.fired_siteU (C := thread P L) (fun _ _ => thread_sound hp) hX he hσ hub
    rw [h, Flow.code_3611] at hc
    cases hc
    rw [h] at hf
    simp only [eventTmpl, Fires] at hf
    obtain ⟨pc, kd⟩ := e
    obtain ⟨-, rfl⟩ := hf.1
    exact hne rfl

/-- **Row `MbarRow.Place`**. -/
theorem mbarRow_place (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : MbarRow.Place P L X := by
  intro g k e l _ he hm
  obtain ⟨pc, kd⟩ := e
  refine event_place hp hX hFw he ?_ ?_
  · rintro f rfl
    simp [Frame.MbarOf] at hm
  · rintro rfl
    simp [Frame.MbarOf] at hm

/-- **Row `BarRow.Place`**. -/
theorem barRow_place (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : BarRow.Place P L X := by
  intro g k e _ he hb
  obtain ⟨pc, kd⟩ := e
  refine event_place hp hX hFw he ?_ ?_
  · rintro f rfl
    simp [Execution.isBar] at hb
  · rintro rfl
    simp [Execution.isBar] at hb

/-- **Row `TmemRow.Place`**. -/
theorem tmemRow_place (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : TmemRow.Place P L X := by
  intro g k e c _ he hk
  refine event_place hp hX hFw he ?_ ?_
  · intro f h; rw [hk] at h; cases h
  · intro h; rw [hk] at h; cases h

/-- **Row `MemRow.Place`**. -/
theorem memRow_place (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : MemRow.Place P L X := by
  intro g k e _ he hm
  refine event_place hp hX hFw he ?_ ?_ <;>
    rcases hm with ⟨a, bs, h⟩ | ⟨a, bs, h⟩ | ⟨a, bs, h⟩ | ⟨a, o, n, h⟩ <;>
    first | (intro f hf; rw [h] at hf; cases hf) | (intro hf; rw [h] at hf; cases hf)

/-- **Where a tensor copy is issued**: a tensor load or store of a launched lane is at a pc of
the code of the role whose lane condition the lane meets. -/
theorem tensor_place (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hk : (∃ a s, e.kind = .tensorIssue a s) ∨ ∃ a s, e.kind = .tensorStore a s) :
    StartupAt e.pc ∨ Wg0At L g e.pc ∨ Wg1At L g e.pc ∨ MmaAt L g e.pc ∨ TmaAt L g e.pc ∨
      IndexAt L g e.pc ∨ DequantAt L g e.pc := by
  have hn : (∀ f, e.kind ≠ .ub f) ∧ e.kind ≠ .exit := by
    rcases hk with ⟨a, s, h⟩ | ⟨a, s, h⟩ <;> rw [h] <;>
      exact ⟨fun f hf => (by cases hf), fun hf => (by cases hf)⟩
  exact event_place hp hX hFw he hn.1 hn.2

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
