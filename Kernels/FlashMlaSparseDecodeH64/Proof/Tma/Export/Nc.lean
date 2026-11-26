-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Tma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.NcApart
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.NcRead
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LenAlloc

@[expose] public section

/-! # The TMA warp's `.nc` reads are allocated

The TMA warp's two `.nc` reads are its length loads (pcs 2181 and 2191), whose pointers are set:
each reads the four bytes of its row of the array (`Tma.topk_read`, `Tma.extra_read`), which
`Pre` allocates (`paramTopkLen`, `paramExtraTopkLen`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The TMA warp's `.nc` read covers allocated bytes only.** -/
theorem tma_ncAlloc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hat : TmaAt L g e.pc) {a : Acc} {bs : List (Option Byte)} (hk : e.kind = .nc a bs)
    (l : Loc) (hc : a.Covers l) : NcRead P m l := by
  have hub : ∀ f, e.kind ≠ .ub f := fun f h => by rw [hk] at h; cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpcσ⟩ := ev_at hp hX hFw he hub
  obtain ⟨-, hlo, hhi⟩ := hat
  obtain ⟨d, n, rfl, -, hso, ⟨-, hK⟩, hl, -⟩ := tma_state hJ hi hev hpcσ ⟨hlo, hhi⟩
  obtain ⟨t, ins, o, hat', hc', hf⟩ : ∃ t ins o, (Tma.code P L g).AtD d t ∧
      kernel.code[(Tma.code P L g).pc d]? = some ins ∧
      Fires ((Tma.code P L g).pc d) (eventTmpl Assumptions.all L g t ins.op) e o := by
    obtain ⟨t, ins, o, hat, -, hc, hf⟩ :=
      Frame.fired_siteU (C := thread P L) (fun _ _ => thread_sound hp) hX he hσ hub
    exact ⟨t, ins, o, hat, hc, hf⟩
  have hs : d.site = .loadTopk ∨ d.site = .loadExtra := by
    unfold Tma.EvK at hK
    revert hK hl
    generalize d.site = s
    intro hK hl
    cases s <;> simp [Tma.Poll, RdAt, hk] at hK ⊢
    all_goals exact absurd rfl (hl _)
  rcases hs with hs | hs
  · obtain ⟨x, hx⟩ := len_ptr (hso.1 hs)
    obtain ⟨bs', hr⟩ := Tma.topk_read hp hx hs hat' hc' hf
    obtain ⟨-, rfl⟩ := Kind.nc.inj (hk.symm.trans hr.1)
    exact len_alloc_topk hp (ctaid_lt hp g).2 hx hk hr l hc
  · obtain ⟨x, hx⟩ := len_ptr (hso.2.1 hs)
    obtain ⟨bs', hr⟩ := Tma.extra_read hp hx hs hat' hc' hf
    obtain ⟨-, rfl⟩ := Kind.nc.inj (hk.symm.trans hr.1)
    exact len_alloc_extra hp (ctaid_lt hp g).2 hx hk hr l hc

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
