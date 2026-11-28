-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DataSound
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Ok
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Pre103
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.EarlyLo
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.FollowW
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PstPack
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PstAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.PstSite
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part006
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part007
import Lemmas.Flow.RoleStep
import Lemmas.Flow.StoreElem
import Lemmas.Kernel.FrameU
import Lemmas.Kernel.UbLast

@[expose] public section

/-! # The bytes of a peer store

The peer store `k` of a lane of warpgroup 0 (pc `403 + 10 k`) writes the 16 bytes of the pack of
the low words `4 k .. 4 k + 3` of its block in progress, the first word lowest
(`w0_pst_value`): the data machine's register facts at the store (`pst_reg0` .. `pst_reg7`) with
the block's low half valid (`W0Early`, once the low half is loaded). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

namespace Wg0
open Wg0.Data

/-- The store's instruction: one 128-bit weak store of register `4031 + k`. -/
private def PstOk (a : MemAccess) (k : Nat) : Prop :=
  a.rule = some .threadAccess ∧ (∃ sp, a.locSpace? = some sp) ∧ (∃ b w, a.addr.base = .reg b w) ∧
    a.kind = .store ∧ a.sem = .weak ∧ a.srcs[0]? = some (.reg (4031 + k)) ∧ a.elem.width = 128

private theorem pstc {pc k : Nat} {a : MemAccess}
    (h : kernel.code[pc]? = some ⟨none, .mem a⟩)
    (hk : PstOk a k := by
      refine ⟨rfl, ⟨_, rfl⟩, ⟨_, _, rfl⟩, rfl, rfl, rfl, rfl⟩) :
    ∃ a, kernel.code[pc]? = some ⟨none, .mem a⟩ ∧ PstOk a k := ⟨a, h, hk⟩

private theorem pst_code (k : Fin 8) :
    ∃ a, kernel.code[403 + 10 * k.val]? = some ⟨none, .mem a⟩ ∧ PstOk a k.val := by
  fin_cases k
  exacts [pstc Flow.code_403, pstc Flow.code_413, pstc Flow.code_423, pstc Flow.code_433,
    pstc Flow.code_443, pstc Flow.code_453, pstc Flow.code_463, pstc Flow.code_473]

end Wg0

open Wg0 Wg0.Data Wg0.Gen in
/-- The register of the peer store `k`: the pack of the block's low words `4 k .. 4 k + 3`. -/
private theorem pst_facts (x : BitVec 64) (b : Blk) {k : Nat} (hk : k < 8) (hlen : b.lo.length = 32)
    (h : ∀ c < 32, halfB (b.lo.getD c (.pred false)) = true) :
    (4031 + k) ∈ (wF x (.pst ⟨k, hk⟩) b).map Prod.fst ∧
      lookupD (wF x (.pst ⟨k, hk⟩) b) (4031 + k) =
        .pair (.pair (b.lo.getD (4 * k) (.pred false)) (b.lo.getD (4 * k + 1) (.pred false)))
          (.pair (b.lo.getD (4 * k + 2) (.pred false)) (b.lo.getD (4 * k + 3) (.pred false))) := by
  interval_cases k
  · exact ⟨by
      show 4031 ∈ (f_pst0 x b.m b.l b.mx b.sk b.lo b.hi b.mw).map Prod.fst
      unfold f_pst0
      rw [List.map_append]
      exact List.mem_append_left _
        (by simp only [pk394_facts1, List.map_cons, List.map_nil]; decide),
      pst_reg0 hlen h⟩
  · exact ⟨by
      show 4032 ∈ (f_pst1 x b.m b.l b.mx b.sk b.lo b.hi b.mw).map Prod.fst
      unfold f_pst1
      rw [List.map_append]
      exact List.mem_append_left _
        (by simp only [pk404_facts1, List.map_cons, List.map_nil]; decide),
      pst_reg1 hlen h⟩
  · exact ⟨by
      show 4033 ∈ (f_pst2 x b.m b.l b.mx b.sk b.lo b.hi b.mw).map Prod.fst
      unfold f_pst2
      rw [List.map_append]
      exact List.mem_append_left _
        (by simp only [pk414_facts1, List.map_cons, List.map_nil]; decide),
      pst_reg2 hlen h⟩
  · exact ⟨by
      show 4034 ∈ (f_pst3 x b.m b.l b.mx b.sk b.lo b.hi b.mw).map Prod.fst
      unfold f_pst3
      rw [List.map_append]
      exact List.mem_append_left _
        (by simp only [pk424_facts1, List.map_cons, List.map_nil]; decide),
      pst_reg3 hlen h⟩
  · exact ⟨by
      show 4035 ∈ (f_pst4 x b.m b.l b.mx b.sk b.lo b.hi b.mw).map Prod.fst
      unfold f_pst4
      rw [List.map_append]
      exact List.mem_append_left _
        (by simp only [pk434_facts1, List.map_cons, List.map_nil]; decide),
      pst_reg4 hlen h⟩
  · exact ⟨by
      show 4036 ∈ (f_pst5 x b.m b.l b.mx b.sk b.lo b.hi b.mw).map Prod.fst
      unfold f_pst5
      rw [List.map_append]
      exact List.mem_append_left _
        (by simp only [pk444_facts1, List.map_cons, List.map_nil]; decide),
      pst_reg5 hlen h⟩
  · exact ⟨by
      show 4037 ∈ (f_pst6 x b.m b.l b.mx b.sk b.lo b.hi b.mw).map Prod.fst
      unfold f_pst6
      rw [List.map_append]
      exact List.mem_append_left _
        (by simp only [pk454_facts1, List.map_cons, List.map_nil]; decide),
      pst_reg6 hlen h⟩
  · exact ⟨by
      show 4038 ∈ (f_pst7 x b.m b.l b.mx b.sk b.lo b.hi b.mw).map Prod.fst
      unfold f_pst7
      rw [List.map_append]
      exact List.mem_append_left _
        (by simp only [pk464_facts1, List.map_cons, List.map_nil]; decide),
      pst_reg7 hlen h⟩

open Wg0 Wg0.Data in
/-- The low half of a block in progress with a loaded low half is valid. -/
private theorem pst_lo {sc : ℝ} {l : List Event} (hv : W0Valid sc l)
    (hne : (w0Words (w0Fin l).2).lo ≠ []) :
    (w0Words (w0Fin l).2).lo.length = 32 ∧
      ∀ c < 32, halfB ((w0Words (w0Fin l).2).lo.getD c (.pred false)) = true := by
  rcases hv.early with h | ⟨w', hw', hlo, -⟩
  · exact absurd (by rw [h]; simp [w0Words, w0Last]) hne
  · have hlo' := hlo.resolve_left hne
    exact ⟨by rw [hlo']; exact hw'.loLen, fun c hc => halfB_lo_early hw' (Or.inr hlo') hc hne⟩

open Wg0 Wg0.Data Wg0.Gen in
/-- **The bytes of a peer store** (valid rows): the store at pc `403 + 10 k0` of lane `g` writes
the 16 bytes of the pack of the low words `4 k0 .. 4 k0 + 3` of the block in progress, the first
word lowest, when the low half of the block is loaded (`hne`). -/
theorem w0_pst_value (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {j k0 : Nat} {e : Event}
    (he : X.get (g, j) = some e) (hk0 : k0 < 8) (hpc : e.pc = 403 + 10 * k0)
    (hv : W0Valid P.scale ((X.tr g).take j))
    (hne : (w0Words (w0Fin ((X.tr g).take j)).2).lo ≠ []) :
    ∀ a bs, e.kind = .wr a bs →
      bs = (Value.pair
        (.pair ((w0Words (w0Fin ((X.tr g).take j)).2).lo.getD (4 * k0) (.pred false))
          ((w0Words (w0Fin ((X.tr g).take j)).2).lo.getD (4 * k0 + 1) (.pred false)))
        (.pair ((w0Words (w0Fin ((X.tr g).take j)).2).lo.getD (4 * k0 + 2) (.pred false))
          ((w0Words (w0Fin ((X.tr g).take j)).2).lo.getD (4 * k0 + 3) (.pred false)))).toBytes := by
  intro a bs hk
  have hub : ∀ f, e.kind ≠ .ub f := fun f h => by rw [hk] at h; cases h
  have hg := Frame.lt_of_get hX he
  have hx := w0_scale_rd hp
  obtain ⟨st, hst, hslot, hpre, hI, -⟩ := followW hp hX hFw hw he hub hx hv j le_rfl
  have hsD := fun g (_ : g < L.threads) => threadD_sound (P := P) (L := L) (g := g) hp
  have hpc' := Frame.event_pcU hsD hX he hst hub
  obtain ⟨t, ins, o, hat, hinv, hcode, hf⟩ := Frame.fired_siteU hsD hX he hst hub
  obtain ⟨q0, n⟩ := st
  rcases hslot with ⟨b, hb⟩ | ⟨d, hd⟩
  · obtain rfl : q0 = .inl b := hb
    have h1 := startup_pc (d := b) (n := n) hinv
    have h2 : e.pc = (thread P L g).pc (.inl b, n) := hpc'
    omega
  obtain rfl : q0 = .inr ⟨.inl .wg0, d⟩ := hd
  obtain ⟨hIW, hOk, -⟩ := hI d rfl
  have hsite : d.c.site = .pst ⟨k0, hk0⟩ := site_pc_pst hk0 (hpc'.symm.trans hpc)
  have hok : d.ok = true := hOk (by rw [hsite]; rfl)
  have hlo := hIW.lo
  rw [← w0Fin_snd] at hlo
  obtain ⟨hlen, hhalf⟩ := pst_lo hv hne
  have hlen' : d.b.lo.length = 32 := by rw [hlo]; exact hlen
  have hh' : ∀ c < 32, halfB (d.b.lo.getD c (.pred false)) = true := by
    rw [hlo]; exact hhalf
  obtain ⟨hmem, hval⟩ := pst_facts (scX L) d.b hk0 hlen' hh'
  obtain ⟨-, hsub, -, -, hF⟩ := hat
  change Holds t.regs (_ ++ dF L d) at hF
  have hF' := ((holds_append _ _ _).mp hF).2
  have hdF : dF L d = wF (scX L) (.pst ⟨k0, hk0⟩) d.b := by
    unfold dF
    simp only [hok, ↓reduceIte, hsite]
  rw [hdF] at hF'
  have hreg := Data.holds_of_mem hF' hmem
  rw [hval] at hreg
  obtain ⟨a', hc', hr', ⟨sp, hs'⟩, ⟨b', w', hb'⟩, hk', hsem', hsrc', hw'⟩ :=
    Wg0.pst_code ⟨k0, hk0⟩
  change kernel.code[d.c.site.pc]? = _ at hcode
  rw [hsite, show (Site.pst ⟨k0, hk0⟩).pc = 403 + 10 * k0 from rfl, hc'] at hcode
  cases hcode
  have hel : d.c.el < 1 := by
    have h1 : d.c.el < Control.elems d.c.site := hinv
    rw [hsite] at h1
    simpa [Control.elems] using h1
  have hs0 : t.sub = 0 := by
    rw [hsub]
    show d.c.el = 0
    omega
  have hb4 : ∀ c < 32, (d.b.lo.getD c (.pred false)).bytes = 4 := fun c hc =>
    halfB_bytes (hh' c hc)
  have hbytes : (Value.pair
      (.pair (d.b.lo.getD (4 * k0) (.pred false)) (d.b.lo.getD (4 * k0 + 1) (.pred false)))
      (.pair (d.b.lo.getD (4 * k0 + 2) (.pred false))
        (d.b.lo.getD (4 * k0 + 3) (.pred false)))).bytes = a'.elem.width / 8 := by
    rw [hw']
    simp only [Value.bytes, hb4 _ (by omega : 4 * k0 < 32), hb4 _ (by omega : 4 * k0 + 1 < 32),
      hb4 _ (by omega : 4 * k0 + 2 < 32), hb4 _ (by omega : 4 * k0 + 3 < 32)]
  obtain ⟨acc, hacc⟩ := fires_st_elemBytes hr' hs' hb' hk' hsem' (by rw [hs0]; exact hsrc')
    hbytes hreg hf hub
  rw [hk] at hacc
  cases hacc
  rw [← hlo]

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
