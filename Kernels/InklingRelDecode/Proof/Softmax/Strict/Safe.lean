-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Strict.SafeB
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.SafeC
import Lemmas.Flow.NoUbSites
import Kernels.InklingRelDecode.Flow.Code.Part008
import Kernels.InklingRelDecode.Flow.Code.Part015
import Kernels.InklingRelDecode.Flow.Code.Part020
import Kernels.InklingRelDecode.Flow.Code.Part035
import Kernels.InklingRelDecode.Flow.Code.Part036

@[expose] public section

/-! # No site of the softmax is undefined behaviour

`safe_soft`: the event template of every site of the softmax but the hand-off to the epilogue, at
a state that holds the facts of its table and the tags of the lane, is not undefined behaviour.
The loads and stores of tensor memory need the broadcast word to name the warp's lane group. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

set_option maxRecDepth 100000

variable {e : Control.Entry} {L : Launch} {g : Nat} {d : Data.D} {t : TState} {ins : Instr}

theorem shfl_sites : ∀ pc ∈ [1261, 1838, 2234, 2242, 2244, 2246, 2248, 2253, 2255],
    shflShape pc = true := by decide +kernel

theorem plain_sites : ∀ pc ∈ [574, 1010, 1298, 2261, 2329], plainShape pc = true := by
  decide +kernel

theorem typed_at (hq : QTF lateQt t) {pc : Nat} (h : t.pc = pc) : TypedF (lateQt pc) t := by
  rw [QTF, h] at hq
  exact hq

/-- **No site of the softmax but the hand-off is undefined behaviour.** -/
theorem safe_soft (hl : SoftLaunch L) (hb : e.base = b32 0) (hrel : e.rel % 2 = 0)
    (hat : (Data.code e L g).AtD d t) (hq : QTF lateQt t) (hs : d.c.site ≠ .epilogue)
    (hx : (d.c.site = .ldS ∨ d.c.site = .ldO ∨ d.c.site = .stO ∨ d.c.site = .tmemSt) →
      Names L g d.c.held.base)
    (hc : kernel.code[d.c.site.pc]? = some ins) (f : Fault) :
    eventTmpl Assumptions.all L g t ins.op ≠ .ub f := by
  have hp : t.pc = d.c.site.pc := hat.1
  have hT := typed_at hq hp
  have plain : plainShape d.c.site.pc = true →
      eventTmpl Assumptions.all L g t ins.op ≠ .ub f := fun h => safe_plain_s hl hc h f
  have shfl : shflShape d.c.site.pc = true →
      eventTmpl Assumptions.all L g t ins.op ≠ .ub f := fun h => safe_shfl_s hl hc h hT f
  have barN : ∀ k, kernel.code[k]? = some ⟨none, .barSyncN (.imm 0) (.imm 128) true⟩ →
      d.c.site.pc = k → eventTmpl Assumptions.all L g t ins.op ≠ .ub f :=
    fun k hk hpk => safe_barN (by
        rw [hpk] at hc
        exact Option.some.inj (hc.symm.trans hk)) f
  cases hsite : d.c.site with
  | setMaxReg => exact plain (by rw [hsite]; exact plain_sites _ (by decide))
  | bar0 =>
    rw [hsite] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_575)
    exact barSync_imm_ok (id := 1) (by decide) f
  | pre j => exact safe_pre hrel hat hsite hc f
  | nxt j => exact safe_nxt hrel hat hsite hc f
  | waitS => exact safe_waitS hl hat hsite hc f
  | shfl4 => exact shfl (by rw [hsite]; exact shfl_sites _ (by decide))
  | ldS => exact safe_ldS hl hb (hx (.inl hsite)) hat hsite hc f
  | waitLd => exact plain (by rw [hsite]; exact plain_sites _ (by decide))
  | shfl5 => exact shfl (by rw [hsite]; exact shfl_sites _ (by decide))
  | shfl6 => exact shfl (by rw [hsite]; exact shfl_sites _ (by decide))
  | waitO => exact safe_waitO hl hat hsite hc f
  | bar22 => exact barN 2241 Flow.code_2241 (by rw [hsite]; rfl)
  | shfl7 => exact shfl (by rw [hsite]; exact shfl_sites _ (by decide))
  | shfl8 => exact shfl (by rw [hsite]; exact shfl_sites _ (by decide))
  | shfl9 => exact shfl (by rw [hsite]; exact shfl_sites _ (by decide))
  | shfl10 => exact shfl (by rw [hsite]; exact shfl_sites _ (by decide))
  | store10 => exact safe_store10 hl hat hq hsite hc f
  | bar23 => exact barN 2251 Flow.code_2251 (by rw [hsite]; rfl)
  | ldL => exact safe_ldL hl hat hsite hc f
  | shfl11 => exact shfl (by rw [hsite]; exact shfl_sites _ (by decide))
  | shfl12 => exact shfl (by rw [hsite]; exact shfl_sites _ (by decide))
  | ldO => exact safe_ldO hl hb (hx (.inr (.inl hsite))) hat hsite hc f
  | waitLdO => exact plain (by rw [hsite]; exact plain_sites _ (by decide))
  | bar24 => exact barN 2326 Flow.code_2326 (by rw [hsite]; rfl)
  | stO => exact safe_stO hl hb (hx (.inr (.inr (.inl hsite)))) hat hq hsite hc f
  | waitStO => exact plain (by rw [hsite]; exact plain_sites _ (by decide))
  | bar20 => exact barN 999 Flow.code_999 (by rw [hsite]; rfl)
  | tmemSt => exact safe_tmemSt hl hb (hx (.inr (.inr (.inr hsite)))) hat hq hsite hc f
  | tmemWait => exact plain (by rw [hsite]; exact plain_sites _ (by decide))
  | bar21 => exact barN 1012 Flow.code_1012 (by rw [hsite]; rfl)
  | arrive => exact safe_arrive hl hat hsite hc f
  | epilogue => exact absurd hsite hs

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
