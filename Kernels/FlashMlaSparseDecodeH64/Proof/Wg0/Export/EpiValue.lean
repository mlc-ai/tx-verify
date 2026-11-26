-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.FollowW
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.EpiRd
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Wg0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Regions
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.OutSeq
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.ScalStore
import Lemmas.Flow.GenStoreElem
import Lemmas.Flow.StoreElem
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DataSound
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Pre103
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Ok
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part008
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part018
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.WordsExt
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumBlk
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part020
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part023
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part025
import Kernels.FlashMlaSparseDecodeH64.Flow.Code.Part028
import Lemmas.Flow.RoleStep
import Lemmas.Flow.StoreElem
import Lemmas.Kernel.FrameU
import Lemmas.Kernel.UbLast

@[expose] public section

/-! # What warpgroup 0's epilogue stores

The staging store `ost2 c j` writes four words of output chunk `c`, each the bf16 pair of two of
the accumulator words the chunk's load returned, times the factor
`w0Fac (w0ESum r l + p) sk m` (`w0EpiF`): from the statistics the loop carried (`m`, `l`, the
true maximum `r`, `CarryW`), the sink word (`InvSk`), the peer's row-sum word `p` and the words
of the chunk's load (`InvE`), all read as numbers over the trace only. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

namespace Wg0
open Wg0.Data

/-- The element `q` of a staging store reads the register of its word. -/
private def OStoreOk (a : MemAccess) (c : Fin 4) (j : Nat) : Prop :=
  a.rule = some .threadAccess ∧ a.locSpace? = none ∧ a.kind = .store ∧
    (∀ q < 4, a.srcs[q]? = some (.reg (eStart c + 3 * (4 * j + q)))) ∧ a.elem.width = 32

private theorem ostc {pc j : Nat} {c : Fin 4} {a : MemAccess}
    (h : kernel.code[pc]? = some ⟨none, .mem a⟩)
    (hk : OStoreOk a c j := by
      refine ⟨rfl, rfl, rfl, fun q hq => ?_, rfl⟩
      match q, hq with
      | 0, _ => rfl
      | 1, _ => rfl
      | 2, _ => rfl
      | 3, _ => rfl) :
    ∃ a, kernel.code[pc]? = some ⟨none, .mem a⟩ ∧ OStoreOk a c j := ⟨a, h, hk⟩

private def LStoreOk (a : MemAccess) : Prop :=
  a.rule = some .threadAccess ∧ (∃ sp, a.locSpace? = some sp) ∧ (∃ b w, a.addr.base = .reg b w) ∧
    a.kind = .store ∧ a.sem = .weak ∧ a.srcs[0]? = some (.reg 1733) ∧ a.elem.width = 32

private theorem lse_code : ∃ a, kernel.code[1178]? = some ⟨none, .mem a⟩ ∧ LStoreOk a :=
  ⟨_, Flow.code_1178, rfl, ⟨_, rfl⟩, ⟨_, _, rfl⟩, rfl, rfl, rfl, rfl⟩

private def EStoreOk (a : MemAccess) : Prop :=
  a.rule = some .threadAccess ∧ (∃ sp, a.locSpace? = some sp) ∧ (∃ b w, a.addr.base = .reg b w) ∧
    a.kind = .store ∧ a.sem = .weak ∧ a.srcs[0]? = some (.reg 1727) ∧ a.elem.width = 32

private theorem est_code : ∃ a, kernel.code[1155]? = some ⟨none, .mem a⟩ ∧ EStoreOk a :=
  ⟨_, Flow.code_1155, rfl, ⟨_, rfl⟩, ⟨_, _, rfl⟩, rfl, rfl, rfl, rfl⟩

private def MStoreOk (a : MemAccess) : Prop :=
  a.rule = some .threadAccess ∧ (∃ sp, a.locSpace? = some sp) ∧ (∃ b w, a.addr.base = .reg b w) ∧
    a.kind = .store ∧ a.sem = .weak ∧ a.srcs[0]? = some (.reg 1109) ∧ a.elem.width = 32

private theorem mst_code : ∃ a, kernel.code[566]? = some ⟨none, .mem a⟩ ∧ MStoreOk a :=
  ⟨_, Flow.code_566, rfl, ⟨_, rfl⟩, ⟨_, _, rfl⟩, rfl, rfl, rfl, rfl⟩

private theorem ostore_code (c : Fin 4) (j : Fin 8) :
    ∃ a, kernel.code[ost2Base c + j.val]? = some ⟨none, .mem a⟩ ∧ OStoreOk a c j.val := by
  fin_cases c <;> fin_cases j
  exacts [
    ostc Flow.code_1331, ostc Flow.code_1332, ostc Flow.code_1333, ostc Flow.code_1334,
    ostc Flow.code_1335, ostc Flow.code_1336, ostc Flow.code_1337, ostc Flow.code_1338,
    ostc Flow.code_1491, ostc Flow.code_1492, ostc Flow.code_1493, ostc Flow.code_1494,
    ostc Flow.code_1495, ostc Flow.code_1496, ostc Flow.code_1497, ostc Flow.code_1498,
    ostc Flow.code_1649, ostc Flow.code_1650, ostc Flow.code_1651, ostc Flow.code_1652,
    ostc Flow.code_1653, ostc Flow.code_1654, ostc Flow.code_1655, ostc Flow.code_1656,
    ostc Flow.code_1806, ostc Flow.code_1807, ostc Flow.code_1808, ostc Flow.code_1809,
    ostc Flow.code_1810, ostc Flow.code_1811, ostc Flow.code_1812, ostc Flow.code_1813]

/-- **The state of a lane at an epilogue site** (`hs`: the site with the event's pc): the statistics
the finished blocks carried, the peer's word and the loads of the block in progress, the sink word,
and the facts of the site hold in the thread's registers. -/
private theorem epi_at (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f) (hge : 103 ≤ e.pc)
    (hv : W0Valid P.scale ((X.tr g).take k)) {s : Site}
    (hs : ∀ s' : Site, s'.pc = e.pc → s' = s) (hin : innerSite s = true)
    (hear : earlyS s = false) :
    ∃ d : D, ∃ (t : TState) (ins : Instr) (o : Option TState), d.c.site = s ∧ d.ok = true ∧
      InvE ((X.tr g).take k) d ∧ InvSk ((X.tr g).take k) d ∧
      Rd d.b.m ((w0Carry P.scale (w0Fin ((X.tr g).take k)).1).1 : ℝ) ∧
      Rd d.b.l ((w0Carry P.scale (w0Fin ((X.tr g).take k)).1).2 : ℝ) ∧
      Rd d.b.mx (w0MxCarry P.scale (w0Fin ((X.tr g).take k)).1) ∧ Scal d.b.l ∧
      Holds t.regs (dF L d) ∧ t.sub = d.c.el ∧ d.c.el < Control.elems s ∧
      kernel.code[s.pc]? = some ins ∧ Fires s.pc (eventTmpl Assumptions.all L g t ins.op) e o ∧
      InvW ((X.tr g).take k) d ∧ ∃ n : Cls → Nat,
        Frame.stateAt (thread P L) X g k = some (some (.inr ⟨.inl .wg0, d.c⟩, n)) := by
  obtain ⟨st, hst, hslot, hpre, hI, -⟩ := followW hp hX hFw hw he hub (w0_scale_rd hp) hv k le_rfl
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
  obtain ⟨hIW, hOk, hCar, hVote, hIE, hSk⟩ := hI d rfl
  have hsite : d.c.site = s := hs _ hpc'.symm
  have hok : d.ok = true := hOk (by rw [hsite]; exact hin)
  obtain ⟨hm, hl, hmx, hsl⟩ := hCar hok (by rw [hsite]; exact hear)
  obtain ⟨-, hsub, -, -, hF⟩ := hat
  change Holds t.regs (_ ++ dF L d) at hF
  have hel : d.c.el < Control.elems d.c.site := hinv
  rw [hsite] at hel
  have h2 : (threadD P L g).pc (.inr ⟨.inl .wg0, d⟩, n) = s.pc := by
    change d.c.site.pc = _
    rw [hsite]
  rw [h2] at hcode hf
  exact ⟨d, t, ins, o, hsite, hok, hIE, hSk, hm, hl, hmx, hsl,
    ((holds_append _ _ _).mp hF).2, hsub, hel, hcode, hf, hIW, n, control_of_data hst⟩

end Wg0

open Wg0 Wg0.Data in
/-- **The words a lane of warpgroup 0 stages** (valid rows): the staging store `ost2 c j` writes
word `4 j + q` of output chunk `c` for some element `q < 4`: the bf16 pair of the accumulator words
`2 w` and `2 w + 1` times the factor `w0EpiF`. The statistics are those of the trace before the
store (`w0Carry`, `w0MxCarry`); the sink word, the peer's row-sum word (the last read at pc 1157)
and the words of the last load of the chunk read as numbers `sk`, `p`, `O i`; a row without a kept
column has no peer sum (`hrp`). -/
theorem w0_ost2_value (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e) {c : Fin 4} {j : Fin 8} (hpc : e.pc = ost2Base c + j.val)
    (hv : W0Valid P.scale ((X.tr g).take k)) {p : ℝ} {sk : EReal} {O : Nat → ℝ}
    (hpe : Rd (w0EpiPe (w0Scan ((X.tr g).take k)).2) (p : EReal)) (hp0 : 0 ≤ p)
    (hsk : Rd (w0SkWord ((X.tr g).take k)) sk)
    (hrp : w0MxCarry P.scale (w0Fin ((X.tr g).take k)).1 = ⊥ → p = 0)
    (hlen : (w0EpiO (w0Scan ((X.tr g).take k)).2).length = 64)
    (hO : ∀ i < 64, Rd ((w0EpiO (w0Scan ((X.tr g).take k)).2).getD i (.pred false)) (O i)) :
    ∀ a bs, e.kind = .wr a bs → ∃ q < 4, a.size = 4 ∧ a.loc = wsLoc L (g / L.block)
        (65536 + 16384 * (tidOf L g / 64) + 128 * (tidOf L g % 64) +
          16 * (j.val ^^^ tidOf L g % 8) + MemRow.wg0OutOff c.val + 4 * q) ∧
      bs = (Assumptions.bf16Pair
      (O (2 * (4 * j.val + q)) * w0EpiF P.scale ((X.tr g).take k) p sk)
      (O (2 * (4 * j.val + q) + 1) * w0EpiF P.scale ((X.tr g).take k) p sk)).toBytes := by
  intro a bs hk
  have hub : ∀ f, e.kind ≠ .ub f := fun f h => by rw [hk] at h; cases h
  have hsite : ∀ s' : Site, s'.pc = e.pc → s' = .ost2 c j := fun s' h =>
    site_pc_ost2 (h.trans hpc)
  have hge : 103 ≤ e.pc := by
    rw [hpc]; fin_cases c <;> simp [ost2Base] <;> omega
  obtain ⟨d, t, ins, o, hds, hok, hIE, hSk, hm, hl, hmx, -, hF, hsub, hel, hcode, hf, -, n0,
      hctl⟩ := epi_at hp hX hFw hw he hub hge hv hsite (by simp [innerSite, onChain, isStart])
      (by simp [earlyS])
  obtain ⟨a', hc', hr', hl', hk', hsrc', hw'⟩ := ostore_code c j
  rw [show (Site.ost2 c j).pc = ost2Base c + j.val from rfl, hc'] at hcode
  cases hcode
  have hdF : dF L d = f_os c.val (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk)) d.b.pe
      d.b.o := by
    unfold dF
    simp only [hok, ↓reduceIte]
    unfold wF wcls
    rw [hds]
    rfl
  have hel4 : d.c.el < 4 := by
    simpa [Control.elems] using hel
  rw [hdF] at hF
  have hmem : eStart c + 3 * (4 * j.val + d.c.el) ∈ (f_os c.val (lookupD (f_car (scX L) d.b.m
      d.b.l d.b.mx d.b.sk)) d.b.pe d.b.o).map Prod.fst := by
    unfold f_os
    rw [List.map_append]
    exact List.mem_append_left _ (es_out_key c _ (by omega))
  have hreg := holds_of_mem hF hmem
  rw [w0e_os_word c (scX L) d.b.m d.b.l d.b.mx d.b.sk d.b.pe d.b.o hm hl hmx (hSk.sk ▸ hsk)
    (hIE.pe ▸ hpe) (w0Carry_l_nonneg _ _) hp0 hrp (hIE.o ▸ hlen) (hIE.o ▸ hO)
    (4 * j.val + d.c.el) (by omega)] at hreg
  have hbytes : (Assumptions.bf16Pair
      (O (2 * (4 * j.val + d.c.el)) * w0EpiF P.scale ((X.tr g).take k) p sk)
      (O (2 * (4 * j.val + d.c.el) + 1) * w0EpiF P.scale ((X.tr g).take k) p sk)).bytes =
      a'.elem.width / 8 := by
    rw [hw']
    simp [Assumptions.bf16Pair, Value.bytes, FloatFmt.bytes]
  obtain ⟨acc, hacc⟩ := fires_gst_elemBytes hr' hl' hk' (by rw [hsub]; exact hsrc' _ hel4)
    hbytes hreg hf hub
  rw [hk] at hacc
  cases hacc
  obtain ⟨σ, hσ, hJ, hi, hev, hpc0⟩ := ev_at hp hX hFw he hub
  obtain ⟨d1, n1, rfl, -, hE, -⟩ := wg0_state hJ hi hev hpc0
    ⟨hge, by rw [hpc]; fin_cases c <;> simp [ost2Base] <;> omega⟩
  rw [hσ] at hctl
  simp only [Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq,
    true_and] at hctl
  obtain ⟨rfl, -⟩ := hctl
  obtain ⟨-, ⟨a2, bs2, hk2, ha2, hl2⟩ | ⟨f, hf2⟩⟩ :=
    Proof.Wg0.ost2_acc hp (MemRow.wg0_tid hw) hds hE.2
  · rw [hk] at hk2
    cases hk2
    exact ⟨d.c.el, hel4, ha2, hl2, rfl⟩
  · exact absurd hf2 (hub f)

open Wg0 Wg0.Data in
/-- **The LSE word a lane of warpgroup 0 stores** (valid rows): the store at pc 1178 writes the
bytes of `w0EpiLse`, from the statistics of the trace before the store and the peer's row-sum
word `p`. -/
theorem w0_lse_value (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hpc : e.pc = 1178)
    (hv : W0Valid P.scale ((X.tr g).take k)) {p : ℝ}
    (hpe : Rd (w0EpiPe (w0Scan ((X.tr g).take k)).2) (p : EReal)) (hp0 : 0 ≤ p) :
    ∀ a bs, e.kind = .wr a bs → bs = (w0EpiLse P.scale ((X.tr g).take k) p).toBytes := by
  intro a bs hk
  have hub : ∀ f, e.kind ≠ .ub f := fun f h => by rw [hk] at h; cases h
  have hsite : ∀ s' : Site, s'.pc = e.pc → s' = .lse := fun s' h => site_pc_1178 (h.trans hpc)
  obtain ⟨d, t, ins, o, hds, hok, hIE, hSk, hm, hl, hmx, -, hF, hsub, hel, hcode, hf, -⟩ :=
    epi_at hp hX hFw hw he hub (by omega) hv hsite (by simp [innerSite, onChain, isStart])
      (by simp [earlyS])
  obtain ⟨a', hc', hr', ⟨sp, hs'⟩, ⟨b', w', hb'⟩, hk', hsem', hsrc', hw'⟩ := lse_code
  rw [show Site.lse.pc = 1178 from rfl, hc'] at hcode
  cases hcode
  have hdF : dF L d = f_lse (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk)) d.b.pe := by
    unfold dF
    simp only [hok, ↓reduceIte]
    unfold wF wcls
    rw [hds]
    rfl
  rw [hdF] at hF
  have hmem : 1733 ∈ (f_lse (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk)) d.b.pe).map
      Prod.fst := by
    unfold f_lse
    rw [List.map_append]
    refine List.mem_append_left _ ?_
    simp only [Gen.e4_facts1, List.map_cons, List.map_nil]
    decide
  have hreg := holds_of_mem hF hmem
  have hw0 := w0e_lse (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk)) d.b.pe (r := _)
    (m := (w0Carry P.scale (w0Fin ((X.tr g).take k)).1).1)
    (l := (w0Carry P.scale (w0Fin ((X.tr g).take k)).1).2) (p := p)
    (by simpa [lookupD, f_car, List.lookup] using hmx)
    (by simpa [lookupD, f_car, List.lookup] using hm)
    (by simpa [lookupD, f_car, List.lookup] using hl) (hIE.pe ▸ hpe)
    (w0Carry_l_nonneg _ _) hp0
  rw [hw0] at hreg
  have hbytes : (w0LseV (w0ESum (w0MxCarry P.scale (w0Fin ((X.tr g).take k)).1)
      (w0Carry P.scale (w0Fin ((X.tr g).take k)).1).2 + p) (w0EMax (w0MxCarry P.scale
      (w0Fin ((X.tr g).take k)).1) (w0Carry P.scale (w0Fin ((X.tr g).take k)).1).1)).bytes =
      a'.elem.width / 8 := by
    rw [hw']
    unfold w0LseV
    split_ifs <;> simp [Value.bytes, FloatFmt.bytes]
  have hel1 : d.c.el = 0 := by
    have : d.c.el < 1 := by simpa [Control.elems] using hel
    omega
  obtain ⟨acc, hacc⟩ := fires_st_elemBytes hr' hs' hb' hk' hsem'
    (by rw [hsub, hel1]; exact hsrc') hbytes hreg hf hub
  rw [hk] at hacc
  cases hacc
  rfl

open Wg0 Wg0.Data in
/-- **The row-sum word a lane of warpgroup 0 exchanges** (valid rows): the store at pc 1155 writes
a word that reads as `w0ESum r l`, the carried sum `l` (zero for a row without a kept column,
`r = w0MxCarry` its true maximum), from the statistics of the trace before the store. -/
theorem w0_est_value (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hpc : e.pc = 1155)
    (hv : W0Valid P.scale ((X.tr g).take k)) :
    ∀ a bs, e.kind = .wr a bs → ∃ v : Value, bs = v.toBytes ∧ Scal v ∧
      Rd v ((w0ESum (w0MxCarry P.scale (w0Fin ((X.tr g).take k)).1)
        (w0Carry P.scale (w0Fin ((X.tr g).take k)).1).2 : ℝ) : EReal) := by
  intro a bs hk
  have hub : ∀ f, e.kind ≠ .ub f := fun f h => by rw [hk] at h; cases h
  have hsite : ∀ s' : Site, s'.pc = e.pc → s' = .est := fun s' h => site_pc_1155 (h.trans hpc)
  obtain ⟨d, t, ins, o, hds, hok, hIE, hSk, hm, hl, hmx, hsl, hF, hsub, hel, hcode, hf, -⟩ :=
    epi_at hp hX hFw hw he hub (by omega) hv hsite (by simp [innerSite, onChain, isStart])
      (by simp [earlyS])
  obtain ⟨a', hc', hr', ⟨sp, hs'⟩, ⟨b', w', hb'⟩, hk', hsem', hsrc', hw'⟩ := est_code
  rw [show Site.est.pc = 1155 from rfl, hc'] at hcode
  cases hcode
  have hdF : dF L d = f_exit (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk)) := by
    unfold dF
    simp only [hok, ↓reduceIte]
    unfold wF wcls
    rw [hds]
    rfl
  rw [hdF] at hF
  have hmem : 1727 ∈ (f_exit (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk))).map
      Prod.fst := by
    unfold f_exit
    rw [List.map_append]
    refine List.mem_append_left _ ?_
    simp only [Gen.e1_facts1, List.map_cons, List.map_nil]
    decide
  have hreg := holds_of_mem hF hmem
  have hw1 := (w0e_e1 (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk)) (r := _)
    (m := (w0Carry P.scale (w0Fin ((X.tr g).take k)).1).1)
    (l := (w0Carry P.scale (w0Fin ((X.tr g).take k)).1).2)
    (by simpa [lookupD, f_car, List.lookup] using hmx)
    (by simpa [lookupD, f_car, List.lookup] using hm)
    (by simpa [lookupD, f_car, List.lookup] using hl)).2
  have hel1 : d.c.el = 0 := by
    have : d.c.el < 1 := by simpa [Control.elems] using hel
    omega
  have hrd : Rd (lookupD (f_exit (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk))) 1727)
      ((w0ESum (w0MxCarry P.scale (w0Fin ((X.tr g).take k)).1)
        (w0Carry P.scale (w0Fin ((X.tr g).take k)).1).2 : ℝ) : EReal) := by
    unfold f_exit
    rw [lk_head_mem (by simp only [Gen.e1_facts1, List.map_cons, List.map_nil]; decide)]
    exact hw1
  have hbytes : (lookupD (f_exit (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk))) 1727).bytes =
      a'.elem.width / 8 := by
    rw [hw']
    exact hrd.1.1
  obtain ⟨acc, hacc⟩ := fires_st_elemBytes hr' hs' hb' hk' hsem'
    (by rw [hsub, hel1]; exact hsrc') hbytes hreg hf hub
  rw [hk] at hacc
  cases hacc
  refine ⟨_, rfl, scal_est_word _ _ _ _ _ hsl, hrd⟩

open Wg0 Wg0.Data in
/-- **The row maximum a lane of warpgroup 0 exchanges** (valid rows): the store at pc 566 writes
a word that reads as `w0Loc` of a valid block `w` that has the block's high words, mask word and
peer pairs (`hhi`, `hmw`, `hpw`: what the store's value depends on), and is a number or negative
infinity (`SK.ni`). The word is scalar. -/
theorem w0_mst_valueW (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hpc : e.pc = 566)
    (hv : W0Valid P.scale ((X.tr g).take k)) {w : W0Words} (hwok : W0Ok P.scale w)
    (hhi : (w0Words (w0Fin ((X.tr g).take k)).2).hi = w.hi)
    (hmw : (w0Words (w0Fin ((X.tr g).take k)).2).mw = w.mw)
    (hpw : ∀ j, (w0Words (w0Fin ((X.tr g).take k)).2).pw j = w.pw j) :
    ∀ a bs, e.kind = .wr a bs → ∃ v : Value, bs = v.toBytes ∧ Scal v ∧
      Rd v (w0Loc P.scale w) ∧ SK.ni.Has v := by
  intro a bs hk
  have hub : ∀ f, e.kind ≠ .ub f := fun f h => by rw [hk] at h; cases h
  have hsite : ∀ s' : Site, s'.pc = e.pc → s' = .mst := fun s' h => site_pc_566 (h.trans hpc)
  obtain ⟨d, t, ins, o, hds, hok, hIE, hSk, hm, hl, hmx, hsl, hF, hsub, hel, hcode, hf, hIW, -⟩ :=
    epi_at hp hX hFw hw he hub (by omega) hv hsite (by simp [innerSite, onChain, isStart])
      (by simp [earlyS])
  obtain ⟨a', hc', hr', ⟨sp, hs'⟩, ⟨b', w', hb'⟩, hk', hsem', hsrc', hw'⟩ := mst_code
  rw [show Site.mst.pc = 566 from rfl, hc'] at hcode
  cases hcode
  have hdF : dF L d = f_mst (scX L) d.b.m d.b.l d.b.mx d.b.sk d.b.lo d.b.hi d.b.mw (d.b.pw 0)
      (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.b.pw 6) (d.b.pw 7) := by
    unfold dF
    simp only [hok, ↓reduceIte]
    unfold wF wcls
    rw [hds]
    rfl
  rw [hdF] at hF
  have hmem : 1109 ∈ (f_mst (scX L) d.b.m d.b.l d.b.mx d.b.sk d.b.lo d.b.hi d.b.mw (d.b.pw 0)
      (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.b.pw 6) (d.b.pw 7)).map
      Prod.fst := by
    unfold f_mst
    rw [List.map_append]
    refine List.mem_append_left _ ?_
    simp only [Gen.rmax_facts2, List.map_cons, List.map_nil]
    decide
  have hreg := holds_of_mem hF hmem
  have hbi : d.b.hi = w.hi := by rw [hIW.hi, ← w0Fin_snd]; exact hhi
  have hbm : d.b.mw = w.mw := by rw [hIW.mw, ← w0Fin_snd]; exact hmw
  have hbp : ∀ j, d.b.pw j = w.pw j := fun j => by rw [hIW.pw, ← w0Fin_snd]; exact hpw j
  have hhas := w0_block_mst_has hwok (w0_scale_rd hp) (b := d.b) (x := scX L) hbi hbm hbp
    hm hl hmx
  have hrd := w0_block_mst hwok (w0_scale_rd hp) (b := d.b) (x := scX L) hbi hbm hbp
    hm hl hmx
  have hbytes : (lookupD (f_mst (scX L) d.b.m d.b.l d.b.mx d.b.sk d.b.lo d.b.hi d.b.mw (d.b.pw 0)
      (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.b.pw 6) (d.b.pw 7)) 1109).bytes =
      a'.elem.width / 8 := by
    rw [hw']
    exact hrd.1.1
  have hel1 : d.c.el = 0 := by
    have : d.c.el < 1 := by simpa [Control.elems] using hel
    omega
  obtain ⟨acc, hacc⟩ := fires_st_elemBytes hr' hs' hb' hk' hsem'
    (by rw [hsub, hel1]; exact hsrc') hbytes hreg hf hub
  rw [hk] at hacc
  cases hacc
  refine ⟨_, rfl, ?_, hrd, hhas⟩
  unfold f_mst
  rw [lk_head_mem (by simp only [Gen.rmax_facts2, List.map_cons, List.map_nil]; decide)]
  exact scal_mst_word _


open Wg0 Wg0.Data in
/-- **The row maximum a lane of warpgroup 0 exchanges** (valid rows): the store at pc 566 of a block
writes a word that reads as the lane's own scaled maximum `w0Loc` of the block's words, which are
valid (`hwok`). The trace `take k'` extends the store's through events at the pcs 566 to 1121
(`hmid`), so its block in progress is the same block with its words complete. -/
theorem w0_mst_value (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {k k' : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hpc : e.pc = 566) (hkk : k ≤ k')
    (hmid : ∀ f ∈ ((X.tr g).take k').drop k, 566 ≤ f.pc ∧ f.pc < 1122)
    (hv : W0Valid P.scale ((X.tr g).take k))
    (hwok : W0Ok P.scale (w0Words (w0Fin ((X.tr g).take k')).2)) :
    ∀ a bs, e.kind = .wr a bs → ∃ v : Value, bs = v.toBytes ∧ Scal v ∧
      Rd v (w0Loc P.scale (w0Words (w0Fin ((X.tr g).take k')).2)) := by
  set ex := ((X.tr g).take k').drop k with hex
  have htk : (X.tr g).take k' = (X.tr g).take k ++ ex := by
    have h1 : ((X.tr g).take k').take k = (X.tr g).take k := by
      rw [List.take_take, Nat.min_eq_left hkk]
    conv_lhs => rw [← List.take_append_drop k ((X.tr g).take k'), h1]
  have hfin : w0Fin ((X.tr g).take k') = ((w0Fin ((X.tr g).take k)).1,
      (w0Fin ((X.tr g).take k)).2 ++ ex) := by
    rw [htk]
    exact w0Fin_ext _ _ (fun f hf' => by
      have := hmid f hf'
      unfold w0ArrSPc w0ArrLPc
      omega)
  obtain ⟨-, hhi, hmw, hpw⟩ :=
    w0Words_ext (w0Fin ((X.tr g).take k)).2 ex (fun f hf' => (hmid f hf').1)
  intro a bs hk
  obtain ⟨v, h1, h2, h3, -⟩ := w0_mst_valueW hp hX hFw hw he hpc hv hwok
    (by rw [hfin]; exact hhi.symm) (by rw [hfin]; exact hmw.symm)
    (fun j => by rw [hfin]; exact (hpw j).symm) a bs hk
  exact ⟨v, h1, h2, h3⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
