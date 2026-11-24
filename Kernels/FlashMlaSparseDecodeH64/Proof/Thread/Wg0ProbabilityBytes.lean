-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PStore

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

open PTX.Flow

noncomputable section

/-- Each firing probability store writes the exact BF16 pair in its abstract role state. -/
theorem fired_pStore_event {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    (hpre : Pre P L mem0) {d : D} {k : Fin 4} {e : Event} {u : TState}
    (hd : d.site = .pStore k) (hf : (code P L g).toMachine.Fired (some d) e (some u)) :
    ∃ a, e.kind = .wr a (pPacked L g d (4 * k.val + d.sub)).toBytes ∧
      siteLoc L g d.site d.block d.sub = some a.loc ∧ a.size = 4 ∧ d.sub < 4 := by
  obtain ⟨t, ht, hfire⟩ := hf
  change (code P L g).AtD d t ∧ Inv P L g d at ht
  change Fires t.pc (match kernel.code[d.site.pc]? with
    | some ins => eventTmpl asms L g t ins.op
    | none => .ub .pcOutOfRange) e (some u) at hfire
  rw [ht.1.1] at hfire
  cases hc : kernel.code[d.site.pc]? with
  | none =>
    rw [hc] at hfire
    cases hfire.2
  | some ins =>
    rw [hc] at hfire
    obtain ⟨a, he, hl, hs⟩ := fires_pStore_packed hpre hd ht.1 ht.2 hc hfire
    exact ⟨a, he, hl, hs, by simpa [hd, Site.elems] using ht.2.subLt⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
