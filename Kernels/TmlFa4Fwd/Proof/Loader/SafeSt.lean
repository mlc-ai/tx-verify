-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Machine
import Kernels.TmlFa4Fwd.Flow.Code.Part007
import Kernels.TmlFa4Fwd.Flow.Code.Part008
import Kernels.TmlFa4Fwd.Flow.Code.Part012
import Kernels.TmlFa4Fwd.Flow.Code.Part014
import Kernels.TmlFa4Fwd.Flow.Code.Part015
import Kernels.TmlFa4Fwd.Flow.Code.Part019
import Kernels.TmlFa4Fwd.Flow.Code.Part022
import Kernels.TmlFa4Fwd.Flow.Code.Part025
import Lemmas.Flow.MemAl
import Kernels.TmlFa4Fwd.Proof.Loader.Shape

@[expose] public section

/-! # The loader warps' local stores are no undefined behaviour

A local store (`st.local.b32` of a page-table round, `st.local.b64` of a pointer round) is located
through THREAD-ACCESS's local rule at its 64-bit address register (`accessAcc_local64`) and faults
only when that address is not aligned to the store. The page-table rounds store at the local
base plus `96 + 4 it` and `64 + 4 it`, the pointer rounds at the local base plus `8 it` or
`32 + 8 it`; the local base is a multiple of 32 (`Pre.localMemory`), so every address is aligned.
The source is a 32-bit or 64-bit word of the table. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat} {ent : Nat → Value}

/-- A weak local store through a 64-bit address register at an aligned address, of a source
register of the element's size, is no undefined behaviour. -/
theorem lst_ok {A : List Assumption} {t : TState} {a : MemAccess} {base : Nat} {x : BitVec 64}
    {f : Fault} (hu : eventTmpl A L g t (.mem a) = .ub f)
    (hrule : a.rule = some .threadAccess) (hd : a.locSpace? = none) (hk : a.kind = .store)
    (hsp : a.space = some .local) (hb : a.addr.base = .reg base 64)
    (hr : t.regs base = some (.bits 64 x)) (hnc : a.nc = false)
    (hgo : a.hints.globalOnly = false) (hv : a.vec = 1) (hsem : a.sem = .weak)
    (hw : a.elem.width / 8 ≠ 0) (hal : wrapAddr 64 x a.addr.off % (a.elem.width / 8) = 0)
    (hsrc : ∃ r v, a.srcs[t.sub]? = some (.reg r) ∧ t.regs r = some v ∧
      v.bytes = a.elem.width / 8) : False := by
  obtain ⟨acc, hacc⟩ := accessAcc_local64 hsp hb hr hnc hgo hv hsem hw hal
  exact accessStore_ok hrule hd hk hacc hsrc f hu

set_option maxHeartbeats 8000000 in
/-- **No local store of a loader lane is undefined behaviour.** -/
theorem lst_safe (hp : Pre p L m) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (h : (code p L g w ent).AtD d t) (hk0 : d.k = 0)
    (hc : kernel.code[(code p L g w ent).pc d]? = some ins)
    (hf : Fires ((code p L g w ent).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    (hs : (∃ per it, d.site = .pgSt per it) ∨ (∃ per it, d.site = .rwSt per it) ∨
      ∃ per b it, d.site = .ptS per b it) (f : Fault) : e.kind ≠ .ub f := by
  have hreg : ∀ r ∈ Flow.live d.site.pc, t.regs r = some (valueOf p L g w ent d r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hsub : t.sub = 0 := by
    have := h.2.1; obtain ⟨s, v, k⟩ := d
    simp only at hk0; subst hk0; simpa using this
  have hlb := hp.localMemory.1
  have hlb2 := hp.localMemory.2.1
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  obtain ⟨site, v, k⟩ := d
  intro hk
  have hu := fires_ub hf hk
  rcases hs with ⟨per, it, rfl⟩ | ⟨per, it, rfl⟩ | ⟨per, b, it, rfl⟩
  · cases per <;>
    · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
      refine lst_ok hu rfl rfl rfl rfl rfl (hreg _ (by lit_mem)) rfl rfl rfl rfl (by decide)
        ?_ ?_
      · show wrapAddr 64 (add64 (BitVec.ofNat 64 (L.localBase + 96))
          (wideU4 (i32 ((it.val : Nat) : Int)))) 0 % 4 = 0
        rw [wideU4_fin, add64_ofNat, wrap_ofNat0]
        have := it.isLt
        omega
      · exact ⟨_, _, by rw [hsub]; rfl, hreg _ (by lit_mem), rfl⟩
  · cases per <;>
    · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
      refine lst_ok hu rfl rfl rfl rfl rfl (hreg _ (by lit_mem)) rfl rfl rfl rfl (by decide)
        ?_ ?_
      · show wrapAddr 64 (add64 (BitVec.ofNat 64 (L.localBase + 64))
          (wideU4 (i32 ((it.val : Nat) : Int)))) 0 % 4 = 0
        rw [wideU4_fin, add64_ofNat, wrap_ofNat0]
        have := it.isLt
        omega
      · exact ⟨_, _, by rw [hsub]; rfl, hreg _ (by lit_mem), by
          simp only [valueOf, values, valuesPgPrime, valuesPgWarm, valuesPgSteady, lookupLit]
          rfl⟩
  · cases per <;> cases b <;>
    · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
      refine lst_ok hu rfl rfl rfl rfl rfl (hreg _ (by lit_mem)) rfl rfl rfl rfl (by decide)
        ?_ ?_
      · first
          | (show wrapAddr 64 (add64 (BitVec.ofNat 64 (L.localBase + 0))
              (shl64 (m64 ((it.val : Nat) : Int)) 3)) 0 % 8 = 0
             rw [shl64_fin3, add64_ofNat, wrap_ofNat0]
             have := it.isLt
             omega)
          | (show wrapAddr 64 (add64 (BitVec.ofNat 64 (L.localBase + 32))
              (shl64 (m64 ((it.val : Nat) : Int)) 3)) 0 % 8 = 0
             rw [shl64_fin3, add64_ofNat, wrap_ofNat0]
             have := it.isLt
             omega)
      · exact ⟨_, _, by rw [hsub]; rfl, hreg _ (by lit_mem), rfl⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
