-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Fits
import Kernels.TmlFa4Fwd.Flow.Code.Part005
import Kernels.TmlFa4Fwd.Flow.Code.Part006
import Kernels.TmlFa4Fwd.Proof.Epilogue.Reads
import Lemmas.Flow.LoadAl
import Kernels.TmlFa4Fwd.Proof.Lib.SchedBand
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader warps' request reads are no undefined behaviour under their reference values

As the MMA warp's (`Mma/Export/SafeRd.lean`): a global word read faults only when misaligned
(`fires_load_reg_al`), and under `LFits` the request's reads address the chosen request's cuQ
words and its used-K word, all 4-aligned. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (chosen)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat} {ent : Nat → Value}

set_option maxHeartbeats 4000000 in
/-- **No request read of a loader lane under its reference values is undefined behaviour.** -/
theorem read_safe (hp : Pre p L m) {d : D} {ns nv nc : Nat} (hF : LFits p L g d ns nv nc)
    {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (h : (code p L g w ent).AtD d t) (hc : kernel.code[(code p L g w ent).pc d]? = some ins)
    (hf : Fires ((code p L g w ent).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    (hs : d.site = .q0 ∨ d.site = .q1 ∨ d.site = .uk) (hk0 : d.k = 0) (f : Fault) :
    e.kind ≠ .ub f := by
  have hreg : ∀ r ∈ Flow.live d.site.pc, t.regs r = some (valueOf p L g w ent d r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hsub : t.sub = 0 := by
    have := h.2.1; obtain ⟨s, v, k⟩ := d
    simp only at hk0; subst hk0; simpa using this
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  have hb := Epilogue.batch_lt hp
  obtain ⟨-, -, -, -, -, -, -, -, hcq, huk, -⟩ := hp.alignment
  have hroom : p.usedKBase + 4 * p.batch ≤ 2 ^ 64 :=
    hp.ranges ⟨p.usedKBase, 4 * p.batch⟩ (by simp [Params.inputRegions])
  have hFE : Epilogue.Fits p L g (toE d) ns nv := by
    unfold LFits at hF
    rw [show lc d.site = .req by rcases hs with h' | h' | h' <;> rw [h'] <;> rfl] at hF
    obtain ⟨-, h1, -⟩ := hF; exact h1
  obtain ⟨R, bal, hC⟩ : ∃ R bal, Epilogue.ChosenVals p L g R bal (toE d) ns nv := by
    rcases hs with h' | h' | h' <;> simp only [Epilogue.Fits, toE, h', Site.epi] at hFE
    · exact hFE
    · obtain ⟨R, bal, h, -⟩ := hFE; exact ⟨R, bal, h⟩
    · obtain ⟨R, bal, h, -⟩ := hFE; exact ⟨R, bal, h⟩
  obtain ⟨i, hi, hib⟩ := Epilogue.chosen_W hp hC
  have hci : chosen d.v.sc = W i := by simpa only [toE] using hi
  obtain ⟨site, v, k⟩ := d
  intro hk
  rcases hs with rfl | rfl | rfl
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    tmpl_unfold hf PTX.loadTmpl
    simp only [PTX.DType.width, PTX.MemAccess.regs, List.filterMap_cons, List.filterMap_nil,
      id] at hf
    have := fires_load_reg_al hsub ((hreg 7515 (by lit_mem)).trans rfl) hf hk
    apply this
    have ha := Epilogue.addrS_toNat0 hp (show i ≤ p.batch by omega)
    simp only [Epilogue.vbits] at ha
    dsimp only
    rw [hci, ha]
    omega
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    tmpl_unfold hf PTX.loadTmpl
    simp only [PTX.DType.width, PTX.MemAccess.regs, List.filterMap_cons, List.filterMap_nil,
      id] at hf
    have := fires_load_reg_al hsub ((hreg 7515 (by lit_mem)).trans rfl) hf hk
    apply this
    have ha := Epilogue.addrS_toNat4 hp hib
    simp only [Epilogue.vbits] at ha
    dsimp only
    rw [hci, ha]
    omega
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    tmpl_unfold hf PTX.loadTmpl
    simp only [PTX.DType.width, PTX.MemAccess.regs, List.filterMap_cons, List.filterMap_nil,
      id] at hf
    have := fires_load_reg_al hsub ((hreg 7516 (by lit_mem)).trans rfl) hf hk
    apply this
    have ha := Mma.addrK_toNat hp hroom (show i < p.batch by omega)
    simp only [Epilogue.vbits] at ha
    dsimp only
    rw [hci, ha]
    omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
