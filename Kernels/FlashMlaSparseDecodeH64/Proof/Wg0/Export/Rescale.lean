-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.RescaleStep
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Epi
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.UbBefore
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.FollowW
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Chain
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Tmem
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.SuccRst
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DataSound
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Pre103
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Ok
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.RescaleFacts
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumBlk
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.TraceE
import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TmemCode
import Lemmas.Flow.TcStVals
import Lemmas.Flow.TcLdLen
import Lemmas.Flow.RoleStep
import Lemmas.Kernel.FrameU
import Lemmas.Kernel.UbLast

@[expose] public section

/-! # What warpgroup 0's rescale stores write

The rescale arm of a block (`Wg0/Control`): chunk `c`'s load of 64 accumulator words, its wait, the
store at pc `814 + 101 c` of the 64 products `x j * s` (the loaded word times the factor `s`, the
number `2 ^ (m - m')` of the block's maxima, or `1`), and its wait. `w0_rescale_step`
(`RescaleStep`): on a valid trace every word a store of the warpgroup wrote is a number if every
register of the load two events before the store read a number. The load, the wait and the store
are consecutive events (`w0_rst_prev`); the products are the facts of the data machine's site
(`rs0_vals` to `rs3_vals`), their factor from the block's values (`blk_alpha`: `1` without a vote,
else the difference of the carried and the new maximum, which are numbers by `w0_block`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- Chunk `c`'s store: 64 source registers, from `1264 + 129 c`. -/
def rstOk (c : Nat) : Bool :=
  match (kernel.code[[814, 915, 1016, 1117].getD c 0]?).map (·.op) with
  | some (PTX.Op.tcSt _ ss TcShape.s32x32b) =>
    ss.length == 64 && (List.range 64).all fun i => ss[i]? == some (.reg (1264 + 129 * c + i))
  | _ => false

/-- **Static check**: the four rescale stores. -/
theorem rstOk_all : (List.range 4).all rstOk = true := by
  decide +kernel

/-- **Static check**: a Tensor Memory store of the kernel is at a rescale store's pc. -/
theorem code_tcSt_pcs : (kernel.code.zip (List.range kernel.code.length)).all (fun q =>
    match q.1.op with
    | PTX.Op.tcSt .. => decide (q.2 ∈ [814, 915, 1016, 1117])
    | _ => true) = true := by
  decide +kernel

/-- Chunk `c`'s load: 64 destination registers, unreduced. -/
def rldOk (c : Nat) : Bool :=
  match (kernel.code[[716, 817, 918, 1019].getD c 0]?).map (·.op) with
  | some (PTX.Op.tcLd ds _ TcShape.s32x32b none) => ds.length == 64
  | _ => false

/-- **Static check**: the four rescale loads. -/
theorem rldOk_all : (List.range 4).all rldOk = true := by
  decide +kernel

/-- A Tensor Memory store of the kernel is chunk `c`'s rescale store. -/
theorem rst_of_code {pc : Nat} {ins : Instr} {ta : Nat} {ss : List Opnd} {sh : TcShape}
    (hc : kernel.code[pc]? = some ins) (hop : ins.op = .tcSt ta ss sh) :
    ∃ c : Fin 4, pc = [814, 915, 1016, 1117].getD c.val 0 := by
  have hm : (ins, pc) ∈ kernel.code.zip (List.range kernel.code.length) := by
    obtain ⟨hlt, hg⟩ := List.getElem?_eq_some_iff.mp hc
    rw [List.mem_iff_getElem?]
    exact ⟨pc, by simp [hlt, hg]⟩
  have h := List.all_eq_true.mp code_tcSt_pcs _ hm
  simp only [hop] at h
  have h' : pc ∈ [814, 915, 1016, 1117] := by simpa using h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
  rcases h' with rfl | rfl | rfl | rfl
  exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]

/-- The sources of chunk `c`'s store. -/
theorem rst_srcs {c : Fin 4} {ins : Instr} {ta : Nat} {ss : List Opnd} {sh : TcShape}
    (hc : kernel.code[[814, 915, 1016, 1117].getD c.val 0]? = some ins)
    (hop : ins.op = .tcSt ta ss sh) :
    sh = .s32x32b ∧ ss.length = 64 ∧ ∀ i < 64, ss[i]? = some (.reg (1264 + 129 * c.val + i)) := by
  have h := List.all_eq_true.mp rstOk_all c.val (List.mem_range.mpr c.isLt)
  simp only [rstOk, hc, hop, Option.map_some] at h
  cases sh <;> simp only [Bool.false_eq_true] at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨rfl, h.1, fun i hi => by simpa using h.2 i hi⟩

/-- The loads of chunk `c` return 64 words. -/
theorem rld_len {c : Fin 4} {ins : Instr} {ds : List Nat} {ta : Nat} {sh : TcShape}
    {red : Option TcLdRed}
    (hc : kernel.code[[716, 817, 918, 1019].getD c.val 0]? = some ins)
    (hop : ins.op = .tcLd ds ta sh red) : sh = .s32x32b ∧ red = none ∧ ds.length = 64 := by
  have h := List.all_eq_true.mp rldOk_all c.val (List.mem_range.mpr c.isLt)
  simp only [rldOk, hc, hop, Option.map_some] at h
  cases sh <;> cases red <;> simp at h
  exact ⟨rfl, rfl, h⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

open Wg0 Wg0.Data in
/-- **The state of a lane at its rescale store**: the data machine's state at chunk `c`'s store,
with the block's reads, the loaded words and the statistics, and its facts in the registers. -/
private theorem rst_at (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hub : ∀ f, e.kind ≠ .ub f) (hge : 103 ≤ e.pc)
    (hv : W0Valid P.scale ((X.tr g).take k)) {c : Fin 4} (hpc : e.pc = (Site.rst c).pc) :
    ∃ (d : D) (t : TState) (ins : Instr) (o : Option TState), d.c.site = .rst c ∧
      d.ok = true ∧ InvE ((X.tr g).take k) d ∧ InvW ((X.tr g).take k) d ∧
      Rd d.b.m ((w0Carry P.scale (w0Fin ((X.tr g).take k)).1).1 : ℝ) ∧
      Rd d.b.l ((w0Carry P.scale (w0Fin ((X.tr g).take k)).1).2 : ℝ) ∧
      Rd d.b.mx (w0MxCarry P.scale (w0Fin ((X.tr g).take k)).1) ∧
      Holds t.regs (dF L d) ∧ kernel.code[(Site.rst c).pc]? = some ins ∧
      Fires (Site.rst c).pc (eventTmpl Assumptions.all L g t ins.op) e o := by
  obtain ⟨st, hst, hslot, hpre, hI, -⟩ :=
    followW hp hX hFw hw he hub (w0_scale_rd hp) hv k le_rfl
  have hsD := fun g (_ : g < L.threads) => threadD_sound (P := P) (L := L) (g := g) hp
  have hpcs := Frame.event_pcU hsD hX he hst hub
  obtain ⟨t, ins, o, hat, hinv, hcode, hf⟩ := Frame.fired_siteU hsD hX he hst hub
  obtain ⟨q0, n⟩ := st
  rcases hslot with ⟨b, hb⟩ | ⟨d, hd⟩
  · obtain rfl : q0 = .inl b := hb
    have h1 := startup_pc (d := b) (n := n) hinv
    have h2 : e.pc = (thread P L g).pc (.inl b, n) := hpcs
    omega
  obtain rfl : q0 = .inr ⟨.inl .wg0, d⟩ := hd
  obtain ⟨hIW, hOk, hCar, -, hIE, -⟩ := hI d rfl
  have hsite : d.c.site = .rst c := Wg0.site_pc_inj (hpcs.symm.trans hpc)
  have hok : d.ok = true := hOk (by rw [hsite]; fin_cases c <;> decide)
  obtain ⟨hm, hl, hmx, -⟩ := hCar hok (by rw [hsite]; fin_cases c <;> decide)
  obtain ⟨-, -, -, -, hF⟩ := hat
  change Holds t.regs (_ ++ dF L d) at hF
  have hpd : (threadD P L g).pc (.inr ⟨.inl .wg0, d⟩, n) = (Site.rst c).pc := by
    change d.c.site.pc = _
    rw [hsite]
  rw [hpd] at hcode hf
  exact ⟨d, t, ins, o, hsite, hok, hIE, hIW, hm, hl, hmx, ((holds_append _ _ _).mp hF).2,
    hcode, hf⟩

/-- The last reading of a block at some pcs is of an event of the block at one of them. -/
private theorem w0Last_mem {α : Type} {f : Event → Option α} {pcs : List Nat} {seg : List Event}
    {v : α} (h : w0Last f pcs seg = some v) : ∃ ev ∈ seg, ev.pc ∈ pcs := by
  unfold w0Last at h
  obtain ⟨ev, hev, hv⟩ := List.mem_filterMap.mp (List.mem_of_getLast? h)
  refine ⟨ev, hev, ?_⟩
  by_contra hn
  simp [hn] at hv

/-- The block of a trace ending with a rescale load and its wait reads the load's words. -/
private theorem epiO_load {l : List Event} {f0 f1 : Event} {a : Nat} {vals : List Value}
    {sh : TcShape} (hk : f0.kind = .tc (.ld a vals sh)) (h0 : f0.pc ∈ w0OPcs)
    (h1 : f1.pc ∉ w0OPcs) (n0 : f0.pc ≠ w0ArrSPc) (n1 : f1.pc ≠ w0ArrSPc) :
    w0EpiO (w0Scan (l ++ [f0, f1])).2 = vals := by
  have e : l ++ [f0, f1] = (l ++ [f0]) ++ [f1] := by simp
  rw [e, w0Scan_snoc, w0Scan_snoc]
  simp only [n0, n1, ite_false]
  unfold w0EpiO w0Last
  simp [List.filterMap_append, h0, h1, w0TcVals, hk]

open Wg0 Wg0.Data in
/-- **A rescale store's words** (valid trace): the store of chunk `c` at its pc has the load of the
chunk two events before it (64 words), and if the load's words read as numbers `y i` then the
store's are `y i * s`, `s = 2 ^ (m - m')` the factor of the block in progress: the carried maximum
`m` and the block's new maximum `m'` (`w0Max`, the same without a vote). -/
theorem w0_rst_vals (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L g < 4) {k : Nat}
    (hv0 : W0Valid P.scale ((X.tr g).take k))
    {e : Event} (he : X.get (g, k) = some e) {c : Fin 4}
    (hpc : e.pc = [814, 915, 1016, 1117].getD c.val 0) {a : Nat} {vals : List Value}
    {sh : TcShape} (hk : e.kind = .tc (.st a vals sh)) :
    ∃ (j : Nat) (f0 : Event) (a0 : Nat) (vals0 : List Value) (sh0 : TcShape), k = j + 2 ∧
      X.get (g, j) = some f0 ∧ f0.kind = .tc (.ld a0 vals0 sh0) ∧ vals0.length = 64 ∧
      ((∀ v ∈ vals0, ∃ r : ℝ, OkF v r) → ∃ (y : Nat → ℝ) (s : ℝ),
        s = (2 : ℝ) ^ ((w0Carry P.scale (w0Fin ((X.tr g).take k)).1).1 -
          w0Max P.scale (w0Carry P.scale (w0Fin ((X.tr g).take k)).1).1
            (w0Words (w0Fin ((X.tr g).take k)).2)) ∧
        (∀ i (hi : i < vals0.length), OkF vals0[i] (y i)) ∧ vals.length = 64 ∧
        ∀ i (hi : i < vals.length), vals[i] = .float .f32 (y i * s)) := by
  have hub : ∀ f, e.kind ≠ .ub f := fun f h => by rw [hk] at h; cases h
  have hrng : ∀ c : Fin 4, 103 ≤ [814, 915, 1016, 1117].getD c.val 0 ∧
      [814, 915, 1016, 1117].getD c.val 0 < 1842 := by decide
  obtain ⟨j, f0, f1, a0, vals0, sh0, rfl, hf0, hpc0, hk0, hf1, hpc1⟩ :=
    w0_rst_prev hp hX hFw hw hv0 he hub hpc
  have hlen : vals0.length = 64 := by
    obtain ⟨ins0, ds, ta, sh', red, hc0, hop0, hl0⟩ :=
      Flow.get_tcLd_len (by rw [hp.block]) hX hf0 hk0
    rw [hpc0] at hc0
    obtain ⟨rfl, rfl, hds⟩ := rld_len hc0 hop0
    rw [hl0 rfl (fun s h => nomatch h), hds]
  refine ⟨j, f0, a0, vals0, sh0, rfl, hf0, hk0, hlen, fun hO => ?_⟩
  obtain ⟨d, t, ins, o, hsite, hok, hIE, hIW, hm, hl, hmx, hF, hcode, hf⟩ :=
    rst_at hp hX hFw hw he hub (by rw [hpc]; exact (hrng c).1) hv0 (c := c) hpc
  -- the block ends with the load and its wait
  have htake : (X.tr g).take (j + 2) = (X.tr g).take j ++ [f0, f1] := by
    have h0 : (X.tr g)[j]? = some f0 := hf0
    have h1 : (X.tr g)[j + 1]? = some f1 := hf1
    rw [show j + 2 = (j + 1) + 1 from rfl, List.take_add_one, List.take_add_one]
    simp [h0, h1]
  have hmem0 : f0.pc ∈ w0OPcs := by
    rw [hpc0]; fin_cases c <;> simp [w0OPcs]
  have hnm1 : f1.pc ∉ w0OPcs := by
    rw [hpc1]; fin_cases c <;> simp [w0OPcs]
  have hn0 : f0.pc ≠ w0ArrSPc := by rw [hpc0]; fin_cases c <;> simp [w0ArrSPc]
  have hn1 : f1.pc ≠ w0ArrSPc := by rw [hpc1]; fin_cases c <;> simp [w0ArrSPc]
  have hoeq : d.b.o = vals0 := by
    rw [hIE.o, htake]
    exact epiO_load hk0 hmem0 hnm1 hn0 hn1
  -- the block is valid when it has voted
  have hvt : d.b.vt = true → W0Ok P.scale (w0Words (w0Scan ((X.tr g).take (j + 2))).2) := by
    intro hvt
    have hw0 := hIW.vt
    rw [hvt] at hw0
    have hs : (w0Last w0VoteOf [578] (w0Scan ((X.tr g).take (j + 2))).2).getD false = true :=
      hw0.symm
    cases hl' : w0Last w0VoteOf [578] (w0Scan ((X.tr g).take (j + 2))).2 with
    | none => rw [hl'] at hs; cases hs
    | some v =>
      obtain ⟨ev, hev, hpcs⟩ := w0Last_mem hl'
      have := hv0.now.2 ⟨ev, by rw [w0Fin_snd]; exact hev, by simpa using hpcs⟩
      rwa [w0Fin_snd] at this
  have hbl : BlkIs d.b (w0Words (w0Scan ((X.tr g).take (j + 2))).2) :=
    ⟨hIW.hi, hIW.mw, hIW.pw, hIW.pm, hIW.vt⟩
  have hdF : dF L d = wF (scX L) (.rst c) d.b := by
    unfold dF; simp only [hok, ↓reduceIte, hsite]
  rw [hdF] at hF
  have hO' : ∀ v ∈ d.b.o, ∃ r : ℝ, OkF v r := by rw [hoeq]; exact hO
  obtain ⟨y, s, hfacts, hyo, hsv⟩ := rst_facts (w0_scale_rd hp) hbl hvt hm hl hmx c
    (by rw [hoeq]; exact hlen) hO'
  rw [hfacts] at hF
  -- the stored words are the products
  have hsh : sh = .s32x32b := by
    have hrow := tmemRow_wg0 hp hX hFw (c := .st a vals sh) (Frame.lt_of_get hX he) he
      ⟨hw, by rw [hpc]; exact (hrng c).1, by rw [hpc]; exact (hrng c).2⟩ hk
    rcases hrow with h | h | h | h | ⟨kk, vs, h⟩ | ⟨cc, vs, h⟩ | ⟨cc, vs, h⟩ | ⟨-, dst, act, h⟩ <;>
      rw [hk] at h <;> simp only [Kind.tc.injEq, reduceCtorEq, TcKind.st.injEq] at h
    exact h.2.2
  subst hsh
  obtain ⟨ta, ss, sh', hop, hvl, hreg⟩ := fires_tcSt_vals hf hk
  obtain ⟨-, hss, hsrc⟩ := rst_srcs hcode hop
  have hl64 : vals.length = 64 := by omega
  refine ⟨y, s, ?_, fun i hi => ?_, hl64, fun i hi => ?_⟩
  · rw [hsv, w0Fin_snd]
  · have := hyo i (by omega)
    rwa [hoeq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at this
  · have hi64 : i < 64 := by omega
    have h1 := hreg i hi _ (hsrc i hi64)
    have h2 := holds_mem ((holds_append _ _ _).mp hF).1 (r := 1264 + 129 * c.val + i)
      (v := .float .f32 (y i * s)) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi64, rfl⟩)
    rw [h1] at h2
    exact Option.some.inj h2

/-- **A rescale store's words are numbers when the words its lane loaded are** (valid traces): every
word a Tensor Memory store of warpgroup 0 wrote to a cell has, two events before the store, a load
of the lane (chunk `c`'s) whose registers, if numbers, make it one. The only stores of the kernel
are the rescale arm's (`code_tcSt_pcs`). -/
theorem w0_rescale_step_at (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {k : Nat}
    (hv : warp L g < 4 → W0Valid P.scale ((X.tr g).take k)) : RescaleStepAt L X (g, k) := by
  rintro cell old ⟨a, vals, sh, jj, ⟨pc, he⟩, hj, -⟩
  have hk : (⟨pc, .tc (.st a vals sh)⟩ : Event).kind = .tc (.st a vals sh) := rfl
  rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, -, hc, hf⟩
  · cases hf
  have hq := fires_tcSt_op hf hk
  obtain ⟨ta, ss, sh', hop⟩ : ∃ ta ss sh', ins.op = .tcSt ta ss sh' := by
    cases hh : ins.op <;> simp only [hh, tcStOp] at hq <;> first | exact ⟨_, _, _, rfl⟩ | cases hq
  obtain ⟨c, hpc⟩ := rst_of_code hc hop
  simp only at hpc
  have hub : ∀ f, (⟨pc, .tc (.st a vals sh)⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  have hrng : 103 ≤ pc ∧ pc < 1842 := by
    rw [hpc]; fin_cases c <;> decide
  obtain ⟨-, -, -, hw⟩ := wg0_at hp hX hFw he hub hrng
  obtain ⟨j, f0, a0, vals0, sh0, rfl, hf0, hk0, -, himp⟩ :=
    w0_rst_vals hp hX hFw hw (hv hw) he hpc hk
  obtain ⟨pc0, kd0⟩ := f0
  simp only at hk0
  subst hk0
  refine ⟨(g, j), a0, vals0, sh0, ⟨pc0, hf0⟩, rfl, by simp, fun hO => ?_⟩
  obtain ⟨y, s, -, -, -, hvals⟩ := himp hO
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.mem_of_getElem? hj)
  rw [hvals i hi]
  exact ⟨_, okF_float _⟩

/-- **The rescale step at every event** from the validity of every warpgroup-0 trace. -/
theorem w0_rescale_step (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X)
    (hv : ∀ g, warp L g < 4 → W0Trace P X g) : RescaleStep L X :=
  fun ⟨_, _⟩ => w0_rescale_step_at hp hX hFw fun hw => (hv _ hw).take _

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
