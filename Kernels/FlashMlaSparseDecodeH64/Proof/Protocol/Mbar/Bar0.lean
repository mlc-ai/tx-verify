-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Startup.Export.Mbar
public import Lemmas.Kernel.BarUpTo
public import Lemmas.Protocol.NamedBarSources

@[expose] public section

/-! # N3: barrier 0 publishes what a thread did before it

The CTA barrier 0 orders an event of a thread `g` before its first barrier-0 event before every
event of a thread `h` of the CTA after its first barrier-0 event (`bar0_pub`, base causality):
`Frame.Handoff.of_bar_upTo_ord` for the named barrier 0 of the CTA's 12 warps with the use bound
`n = 1`, where each thread's first barrier-0 event is `bar.sync 0` of the whole CTA
(`startup_bar0`).

**Input (`Bar0Rows`, not an export yet).** The handoff needs two facts of every thread's whole
trace, not only its startup part:

* `count`: every arrival on barrier 0 of a launched thread passes no thread count (the roles after
  the startup use named barriers whose ids are registers, so this is a row of each role: its
  barrier events name a barrier other than 0, or barrier 0 without a count; owed by every role
  lane, through a `Common/Export` bar row);
* `exit`: a thread's `exit` follows a barrier-0 event of it (the startup has no `exit` before its
  `bar.sync 0`; owed by lane A, from `startup_view`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The barrier-0 rows the publication needs** (proposed exports; see the header). -/
structure Bar0Rows (L : Launch) (X : Execution) : Prop where
  count : ∀ {e : EvId} {pc : Nat} {cnt : Option Nat}, X.IsBarArrival e 0 cnt pc →
    e.1 < L.threads → cnt = none
  exit : ∀ {g j pc : Nat}, g < L.threads → X.get (g, j) = some ⟨pc, .exit⟩ →
    0 < ((X.tr g).take j).countP isBar0

theorem isBar0_eq : isBar0 = Execution.isBarId 0 := by
  funext e
  obtain ⟨pc, k⟩ := e
  cases k <;> try rfl
  rename_i id _ _
  cases id <;> rfl

/-- Barrier 0's arrivals: every launched thread of the CTA's 12 warps, without a count. -/
theorem bar0_sources (hp : Pre P L m) (hB : Bar0Rows L X) :
    NamedBar.Sources L X none (Finset.range 12) 0 := fun e pc cnt ha hlt => by
  have hb := hp.block
  refine ⟨Finset.mem_range.mpr ?_, hB.count ha hlt⟩
  rw [hb]
  omega

/-- Barrier 0's shape: the 12 warps of the CTA. -/
theorem bar0_shape (hp : Pre P L m) : NamedBar.Shape L none (Finset.range 12) 0 :=
  have hb := hp.block
  { pos := by simp
    target := by rw [hb]; rfl
    bound := fun w hw => by rw [hb]; simpa using hw
    id_lt := by decide }

/-- **N3: barrier 0's publication.** An event of `g` before its first barrier-0 event happens
before every event of a thread `h` of its CTA after `h`'s first barrier-0 event. -/
theorem bar0_pub (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hB : Bar0Rows L X) {g h e f : Nat} (hcta : SameCta L g h)
    (he0 : ((X.tr g).take (e + 1)).countP isBar0 = 0) (hf : f < (X.tr h).length)
    (hf0 : 0 < ((X.tr h).take f).countP isBar0) :
    baseCausality L X (g, e) (h, f) := by
  have hb := hp.block
  have hS := bar0_sources hp hB
  have hG := bar0_shape (L := L) hp
  have H := Frame.Handoff.of_bar_upTo_ord hX hS hG (syncs := fun _ => True)
    (prod := fun _ => True) 1
    (fun h' j pc cnt mode _ he hlt => by
      rw [← isBar0_eq] at hlt
      exact (startup_bar0 hp hX hFw he rfl (by omega)).2.1)
    (fun g' hg' _ _ ⟨j, pc, hx⟩ => by
      have h1 := hB.exit hg' hx
      have h2 : ((X.tr g').take j).countP isBar0 ≤ (X.tr g').countP isBar0 :=
        (List.take_sublist _ _).countP_le
      rw [← isBar0_eq]
      omega)
  refine H g h e f ⟨hcta, ?_, trivial, trivial⟩ hf ?_
  · obtain ⟨hgt, -, -⟩ := hcta
    have : g % L.block < L.block := Nat.mod_lt _ (by omega)
    rw [Finset.mem_range]
    omega
  · simp only [← isBar0_eq]
    omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
