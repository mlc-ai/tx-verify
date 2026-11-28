-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Dequant
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.NcApart
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantWords
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.NcRead
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LenAlloc

@[expose] public section

/-! # Warpgroup 2's `.nc` reads are allocated

Warpgroup 2's two `.nc` reads are its length loads (pcs 2620 and 2630), whose pointers are set
(`deqWordsOk`): each reads the four bytes of its row of the array (`Dequant.Control.topk_read`,
`Dequant.Control.extra_read`), which `Pre` allocates (`paramTopkLen`, `paramExtraTopkLen`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Warpgroup 2's `.nc` read covers allocated bytes only.** -/
theorem dequant_ncAlloc (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hat : DequantAt L g e.pc) {a : Acc} {bs : List (Option Byte)} (hk : e.kind = .nc a bs)
    (l : Loc) (hc : a.Covers l) : NcRead P m l := by
  have hub : ∀ f, e.kind ≠ .ub f := fun f h => by rw [hk] at h; cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpcσ⟩ := ev_at hp hX hFw he hub
  obtain ⟨-, -, hlo, hhi⟩ := hat
  obtain ⟨d, n, rfl, -, ⟨-, hK⟩, -, -⟩ := dequant_state hp hJ hi hev hpcσ ⟨hlo, hhi⟩
  have hok := deq_words hp hX hσ d n rfl
  obtain ⟨t, ins, o, hat', hinv, hc', hf⟩ := deq_fired hp hX he hub hσ
  have hs : d.site = .lenA ∨ d.site = .lenB := by
    unfold Dequant.EvK at hK
    revert hK
    generalize d.site = s
    intro hK
    cases s <;> simp [Dequant.PollEv, Dequant.LoadEv, Dequant.StoreEv, hk] at hK ⊢
  rcases hs with hs | hs
  · simp only [deqWordsOk, hs] at hok
    obtain ⟨x, hx⟩ := len_ptr hok.1
    obtain ⟨bs', hr⟩ := Dequant.Control.topk_read hp hx hs hat' hinv hc' hf
    obtain ⟨-, rfl⟩ := Kind.nc.inj (hk.symm.trans hr.1)
    exact len_alloc_topk hp (ctaid_lt hp g).2 hx hk hr l hc
  · simp only [deqWordsOk, hs] at hok
    obtain ⟨x, hx⟩ := len_ptr hok.1
    obtain ⟨bs', hr⟩ := Dequant.Control.extra_read hp hx hs hat' hinv hc' hf
    obtain ⟨-, rfl⟩ := Kind.nc.inj (hk.symm.trans hr.1)
    exact len_alloc_extra hp (ctaid_lt hp g).2 hx hk hr l hc

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
