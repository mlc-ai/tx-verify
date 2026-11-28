-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data.Kinds
public import Lemmas.Flow.RunFrame

@[expose] public section

/-! # Strict twins of the data runs: the shared lemmas

The generated twins (`Dequant/Gen/DataSegs*.lean`) state the run between two events of a data site
as an exact segment (`Seg`), from the facts after the event to the successor's facts, control facts
included: the run reads and writes data registers only, so the successor's control facts are carried
across it (`SegD.frame`). `SegD.strict` turns a run under its condition into such a segment, and
`ctl_sub` gives the control facts the frame carries from those the state has. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

/-- Facts that are among those of a holding list hold. -/
theorem holds_sub {R : Nat → Option Value} {F F' : List (Nat × Value)} (h : Holds R F')
    (hs : ∀ x ∈ F, x ∈ F') : Holds R F :=
  holds_of_mem fun _ _ hm => holds_mem h (hs _ hm)

/-- Facts of the state's value table over registers live at its site are among its control
facts. -/
theorem ctl_sub {P : Params} {L : Launch} {g : Nat} {c : Control.D} {s : Site} {l : List Nat}
    (hc : c.site = s) (hl : ∀ r ∈ l, r ∈ Control.ctlLive s.pc) :
    ∀ x ∈ factsFrom l (Control.valueOf P L g c), x ∈ Control.facts P L g c := by
  intro x hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
  exact List.mem_map.mpr ⟨r, by rw [hc]; exact hl r hr, rfl⟩

/-- The facts over live registers: those not written by a run, and those it wrote. -/
theorem holds_ctl_split {R : Nat → Option Value} {live W : List Nat} {v : Nat → Value}
    (hH : Holds R (factsFrom (live.filter fun r => !W.contains r) v))
    (hW : ∀ r ∈ W, R r = some (v r)) : Holds R (factsFrom live v) := by
  refine holds_of_mem fun r x hm => ?_
  obtain ⟨r', hr', hx⟩ := List.mem_map.mp hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
  by_cases hw : r' ∈ W
  · exact hW r' hw
  · exact holds_mem hH (mem_factsFrom (List.mem_filter.mpr ⟨hr', by simpa using hw⟩))

/-- A run under its condition, as an exact segment between restated facts. -/
theorem SegD.strict {K : Kernel} {A : List Assumption} {L : Launch} {g n s b : Nat}
    {F F' G G' : List (Nat × Value)} {C : Prop} (h : SegD K A L g n s F b G C) (hC : C)
    (hF : ∀ R, Holds R F' → Holds R F) (hG : ∀ R, Holds R G → Holds R G') :
    ∃ n, Seg K A L g n s F' b G' :=
  ⟨n, ((h.seg hC).weaken_end hG).weaken_start hF⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data
