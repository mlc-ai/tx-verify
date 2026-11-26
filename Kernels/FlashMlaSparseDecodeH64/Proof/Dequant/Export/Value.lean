-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.DqValue
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Numeric.Dequant
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DataSound
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Data.Trace
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.FollowD
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part043
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part044
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part045
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part046
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part047
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part048
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part049
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part050
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part051
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part052
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part053
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part054
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part055
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part056
import Lemmas.Flow.RoleStep
import Lemmas.Flow.StoreSrc
import Lemmas.Kernel.FrameU
import Lemmas.Kernel.UbLast

@[expose] public section

/-! # The chunk a dequantizer lane stores

`dq_store_value`: on valid data (`DqValid`), the bytes a lane of warps 8–11 stores at chunk
`(r, s)` (pc `dqStorePc r s`) are those of `dequantChunk x b`, where `x` is the raw word its last
load at `dqRawPc r s` read and `b` is byte `2 s + [lane % 8 ≥ 4]` of the sixteen scale bytes its
last four loads at `dqScalePc r` read, all rebuilt from the bytes read (`Iface/DqValue.lean`).

The proof runs the data thread machine `threadD` privately: on valid data it follows the lane
wherever the control machine does (`followD`, by induction from `Follow`: the control state at
each prefix is the erased data state, `control_of_data`, and the data step exists by
`dataNext_ok`), and its words are the trace's last loads (`Dequant.Data.InvD`). At the store, the
source register holds the chunk of the data facts (`dF`), and the store writes its bytes
(`fires_st_srcBytes`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Numeric.Dequant MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

namespace Dequant
open Dequant.Data

/-- The store's instruction: a one-source weak shared store of the chunk register. -/
private def StoreOk (a : MemAccess) (src : Nat) : Prop :=
  a.rule = some .threadAccess ∧ (∃ sp, a.locSpace? = some sp) ∧ (∃ b w, a.addr.base = .reg b w) ∧
    a.kind = .store ∧ a.sem = .weak ∧ a.srcs = [.reg src] ∧ a.elem.width = 128

private theorem stc {pc src : Nat} {a : MemAccess} (h : kernel.code[pc]? = some ⟨none, .mem a⟩)
    (hk : StoreOk a src := by exact ⟨rfl, ⟨_, rfl⟩, ⟨_, _, rfl⟩, rfl, rfl, rfl, rfl⟩) :
    ∃ a, kernel.code[pc]? = some ⟨none, .mem a⟩ ∧ StoreOk a src := ⟨a, h, hk⟩

private theorem store_code (r : Fin 4) (s : Fin 8) :
    ∃ a, kernel.code[dqStorePc r s]? = some ⟨none, .mem a⟩ ∧ StoreOk a (chunkReg r s) := by
  fin_cases r <;> fin_cases s
  exacts [
    stc Flow.code_2752, stc Flow.code_2776, stc Flow.code_2800, stc Flow.code_2824,
    stc Flow.code_2848, stc Flow.code_2872, stc Flow.code_2896, stc Flow.code_2919,
    stc Flow.code_2977, stc Flow.code_3001, stc Flow.code_3025, stc Flow.code_3049,
    stc Flow.code_3073, stc Flow.code_3097, stc Flow.code_3121, stc Flow.code_3144,
    stc Flow.code_3202, stc Flow.code_3226, stc Flow.code_3250, stc Flow.code_3274,
    stc Flow.code_3298, stc Flow.code_3322, stc Flow.code_3346, stc Flow.code_3369,
    stc Flow.code_3427, stc Flow.code_3451, stc Flow.code_3475, stc Flow.code_3499,
    stc Flow.code_3523, stc Flow.code_3547, stc Flow.code_3571, stc Flow.code_3594]

private theorem hiSel_tab : ∀ t < 384,
    Arith32.scmpi .gt .u (Arith32.andi (BitVec.ofNat 64 t) 7) 3 = !decide (t % 8 < 4) := by
  decide +kernel

private theorem selByte_eq (hp : Pre P L m) (sc s : Nat) :
    selByte L g sc s = byteAt sc (2 * s + if g % 8 < 4 then 0 else 1) := by
  have h := hiSel_tab (g % 384) (Nat.mod_lt _ (by decide))
  rw [Nat.mod_mod_of_dvd _ (by decide : 8 ∣ 384)] at h
  have he : hiSel L g = !decide (g % 8 < 4) := by
    rw [← h, hiSel, Control.r55W, tw, tidOf_eq hp]
  unfold selByte
  rw [he]
  by_cases h4 : g % 8 < 4 <;> simp [h4]

private theorem site_store {x : Site} {r s : Nat} (hr : r < 4) (hs : s < 8)
    (h : x.pc = dqStorePc r s) : x = .store ⟨r, hr⟩ ⟨s, hs⟩ := by
  cases x with
  | store r' s' =>
    have := r'.isLt; have := s'.isLt
    rw [store_pc] at h
    unfold dqStorePc at h
    obtain ⟨h1, h2⟩ : r'.val = r ∧ s'.val = s := by split_ifs at h <;> omega
    subst h1 h2; rfl
  | raw r' s' =>
    exact absurd (by rw [store_pc, ← h, raw_pc]) (store_ne_raw ⟨r, hr⟩ r' ⟨s, hs⟩ s')
  | scale r' =>
    exact absurd (by rw [store_pc, ← h, scale_pc]) (store_ne_scale ⟨r, hr⟩ r' ⟨s, hs⟩)
  | _ => simp only [Site.pc, dqStorePc] at h; split_ifs at h <;> omega

end Dequant

open Dequant Dequant.Data in
/-- **The chunk a dequantizer lane stores** (valid data): the bytes of chunk `(r, s)` are those
of `dequantChunk x b`, with `x` the raw word the lane's last load at `dqRawPc r s` read and `b`
byte `2 s + [lane % 8 ≥ 4]` of the scale bytes its last four loads at `dqScalePc r` read. -/
theorem dq_store_value (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : 8 ≤ warp L g ∧ warp L g < 12) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e) {r s : Nat} (hr : r < 4) (hs : s < 8)
    (hpc : e.pc = dqStorePc r s) (hv : DqValid X g k) :
    ∀ a bs, e.kind = .wr a bs → bs = (dequantChunk (rawWordOf (lastAt X g k (dqRawPc r s) 1))
      (byteAt (scaleWordOf (lastAt X g k (dqScalePc r) 4))
        (2 * s + if g % 8 < 4 then 0 else 1))).toBytes := by
  intro a bs hk
  have hub : ∀ f, e.kind ≠ .ub f := fun f h => by rw [hk] at h; cases h
  have hg := Frame.lt_of_get hX he
  obtain ⟨st, hst, hI, -⟩ := followD hp hX hFw hw he (by
    obtain ⟨σk, hσk, -⟩ := ev_at hp hX hFw he hub
    exact ⟨σk, hσk⟩) hv k le_rfl
  have hsD := fun g (_ : g < L.threads) => threadD_sound (P := P) (L := L) (g := g) hp
  have hpc' := Frame.event_pcU hsD hX he hst hub
  obtain ⟨t, ins, o, hat, hinv, hcode, hf⟩ := Frame.fired_siteU hsD hX he hst hub
  obtain ⟨q, n⟩ := st
  rcases deq_slot hFw hw hg hst with ⟨b, hb⟩ | ⟨d, hd⟩
  · obtain rfl : q = .inl b := hb
    obtain ⟨σ, hσ, hJ, hi, hev, hpcσ⟩ := ev_at hp hX hFw he hub
    rw [control_of_data hst] at hσ
    cases hσ
    have hrange : 2606 ≤ e.pc ∧ e.pc < 3611 := by rw [hpc]; unfold dqStorePc; split_ifs <;> omega
    obtain ⟨d, n', h, -⟩ := dequant_state hp hJ hi hev hpcσ hrange
    cases h
  obtain rfl : q = .inr ⟨.inl .dequant, d⟩ := hd
  have hsite : d.c.site = .store ⟨r, hr⟩ ⟨s, hs⟩ := site_store hr hs (hpc'.symm.trans hpc)
  obtain ⟨-, hsub, -, -, hF⟩ := hat
  change Holds t.regs (_ ++ dF L g d) at hF
  have hF' := ((holds_append _ _ _).mp hF).2
  simp only [dF, hsite, holds_append] at hF'
  obtain ⟨-, hreg, -⟩ := hF'
  have hel : d.c.el = 0 := by
    have h1 : d.c.el < Control.elems d.c.site := hinv
    rw [hsite] at h1; simpa [Control.elems] using h1
  obtain ⟨a', hc', hr', ⟨sp, hs'⟩, ⟨b, w, hb'⟩, hk', hsem', hsrc', hw'⟩ :=
    store_code ⟨r, hr⟩ ⟨s, hs⟩
  change kernel.code[d.c.site.pc]? = _ at hcode
  rw [hsite, store_pc, hc'] at hcode
  cases hcode
  obtain ⟨acc, hacc⟩ := fires_st_srcBytes hr' hs' hb' hk' hsem' hsrc'
    (by rw [hw']; exact dequantChunk_width _ _) (hsub.trans hel) hreg hf hub
  rw [hk] at hacc
  cases hacc
  rw [chunkVal, selByte_eq hp, hI d rfl |>.ws ⟨r, hr⟩ ⟨s, hs⟩ (by rw [hsite]; simp [Done]),
    hI d rfl |>.sc ⟨r, hr⟩ (by rw [hsite]; simp [InRow])]
  rfl

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
