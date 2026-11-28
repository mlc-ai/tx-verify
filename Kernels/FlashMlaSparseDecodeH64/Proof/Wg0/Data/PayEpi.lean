-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.EarlyLo
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NoUb
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumVoteIn
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Pre103
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.StrictPeer
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.WinEpi
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.WinRes
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.PstPack
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.SuccRst
import Kernels.FlashMlaSparseDecodeH64.Flow.Code

@[expose] public section

/-! # The payload registers of the epilogue's stores

The row-sum store (pc 1155, register 1727) and the log-sum-exp store (pc 1178, register 1733)
write four-byte words, and so does each staging store (`ost2 c j`, registers
`eStart c + 3 (4 j + i)`): packed bf16 pairs. -/

/-! # The payload registers of the probability stores and of the Tensor Memory stores

At the probability store `k` (pc `704 + k`) the registers `1115 + 12 k + 3 i` hold packed bf16
pairs (four bytes); at the rescale's Tensor Memory store `c` the 64 registers
`1264 + 129 c + j` hold the products of the loaded words and the factor (four-byte numbers). -/

/-! # The payload registers of the peer stores, the row-maximum store and the vote

At the peer store `k` (pc `403 + 10 k`) the register `4031 + k` holds the 16-byte pack of the
block's low words; at the row-maximum store (pc 566) register 1109 holds a four-byte word; at the
vote (pc 578) register 109 holds a predicate. -/

/-! # What the payload registers of a site have to hold

`needsOf ins`: the registers a store or a Tensor Memory store reads, with the byte width of the
value each holds; `predNeeds ins`: the registers of the vote's predicate. `payAll_of_needs`: the
payload obligation `PayAll` of the instruction from facts of the registers that hold them. The
sites that read no payload are free (`free_sites`): the table is decided once for all sites. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

noncomputable section

/-- The registers an operand list names. -/
def regsOf : List Opnd → List Nat :=
  List.filterMap fun o => match o with
    | .reg r => some r
    | _ => none

theorem mem_regsOf {r : Nat} {l : List Opnd} : r ∈ regsOf l ↔ Opnd.reg r ∈ l := by
  unfold regsOf
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨o, ho, h⟩
    cases o <;> simp at h
    subst h
    exact ho
  · intro h
    exact ⟨_, h, rfl⟩

/-- The registers (with byte widths) a store or tensor store of the instruction reads. -/
def needsOf (ins : Instr) : List (Nat × Nat) :=
  match ins.op with
  | .mem a => (regsOf a.srcs).map fun r => (r, a.elem.width / 8)
  | .tcSt _ ss _ => (regsOf ss).map fun r => (r, 4)
  | _ => []

/-- The registers of a vote's predicate. -/
def predNeeds (ins : Instr) : List Nat :=
  match ins.op with
  | .warp wi => regsOf wi.srcs
  | _ => []

/-- **The payload obligation** from the registers' values. -/
theorem payAll_of_needs {t : TState} {ins : Instr}
    (h1 : ∀ r n, (r, n) ∈ needsOf ins → ∃ v, t.regs r = some v ∧ v.bytes = n)
    (h2 : ∀ r, r ∈ predNeeds ins → ∃ p, t.regs r = some (.pred p)) : PayAll t ins := by
  refine ⟨fun a ha r hr => ?_, fun ta ss sh hop r hr => ?_, fun wi hop r hr => ?_⟩
  · exact h1 r _ (by simp [needsOf, ha, mem_regsOf.mpr hr])
  · exact h1 r 4 (by simp [needsOf, hop, mem_regsOf.mpr hr])
  · exact h2 r (by simp [predNeeds, hop, mem_regsOf.mpr hr])

/-- A site that reads a payload. -/
def paySite : Site → Bool
  | .pst _ | .mst | .vote | .ost _ | .rst _ | .est | .lse | .ost2 _ _ => true
  | _ => false

/-- Whether the instruction at a pc reads no payload. -/
def freeB (p : Nat) : Bool :=
  match kernel.code[p]? with
  | some ins => (needsOf ins).isEmpty && (predNeeds ins).isEmpty
  | none => true

/-- **The sites that read no payload** are free. -/
theorem free_sites : ∀ s ∈ allSites, paySite s = false → freeB s.pc = true := by
  decide +kernel

theorem pay_of_free {t : TState} {ins : Instr} {s : Site} (hs : paySite s = false)
    (hc : kernel.code[s.pc]? = some ins) : PayAll t ins := by
  have h := free_sites s (mem_allSites s) hs
  simp only [freeB, hc, Bool.and_eq_true, List.isEmpty_iff] at h
  refine payAll_of_needs (fun r n hm => ?_) (fun r hm => ?_)
  · rw [h.1] at hm; simp at hm
  · rw [h.2] at hm; simp at hm

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen
  PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {L : Launch} {g : Nat} {sc : ℝ} {l : List Event} {d : D} {e : Event}

/-- The data facts of a state on a site of the chain are its site's. -/
theorem dF_site (c : WCtx L g sc l d e) {s : Site} (hs : d.c.site = s) (hi : innerSite s = true) :
    dF L d = wF (scX L) s d.b := by
  have hok : d.ok = true := c.hOk (by rw [hs]; exact hi)
  unfold dF
  simp [hok, hs]

/-- A register whose looked-up word is not the default is a fact's. -/
theorem mem_of_lookupD_ne {F : List (Nat × Value)} {r : Nat} (h : lookupD F r ≠ .bits 32 0) :
    r ∈ F.map Prod.fst := by
  by_contra hm
  apply h
  induction F with
  | nil => rfl
  | cons p F ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at hm
    have hk : (r == k) = false := by simpa using hm.1
    simp only [lookupD, List.lookup, hk] at *
    exact ih (by simpa [lookupD] using h) hm.2

/-- The value of the register of the peer store `k`. -/
theorem pst_facts_val (x : BitVec 64) (b : Blk) (k : Fin 8) (hlen : b.lo.length = 32)
    (h : ∀ c < 32, halfB (b.lo.getD c (.pred false)) = true) :
    lookupD (wF x (.pst k) b) (4031 + k.val) =
      .pair (.pair (b.lo.getD (4 * k.val) (.pred false)) (b.lo.getD (4 * k.val + 1) (.pred false)))
        (.pair (b.lo.getD (4 * k.val + 2) (.pred false))
          (b.lo.getD (4 * k.val + 3) (.pred false))) := by
  fin_cases k
  exacts [pst_reg0 hlen h, pst_reg1 hlen h, pst_reg2 hlen h, pst_reg3 hlen h, pst_reg4 hlen h,
    pst_reg5 hlen h, pst_reg6 hlen h, pst_reg7 hlen h]

/-- **The peer store's payload**: a 16-byte word. -/
theorem pay_pst (c : WCtx L g sc l d e) (k : Fin 8) (hs : d.c.site = .pst k) {t : TState}
    (hF : Holds t.regs (dF L d)) : ∃ v, t.regs (4031 + k.val) = some v ∧ v.bytes = 16 := by
  have hp : e.pc = 403 + 10 * k.val := by rw [c.hpc, hs]; rfl
  obtain ⟨w', hw', -, hlo, -⟩ := c.canon (by omega) (by omega)
  rw [dF_site c hs (by simp [innerSite, onChain, isStart])] at hF
  have hh : ∀ i < 32, halfB (d.b.lo.getD i (.pred false)) = true := fun i hi => by
    rw [hlo]; exact halfB_lo hw' hi
  have hval := pst_facts_val (scX L) d.b k (by rw [hlo]; exact hw'.loLen) hh
  have hreg := Wg0.Data.holds_of_mem hF (mem_of_lookupD_ne (by rw [hval]; simp))
  rw [hval] at hreg
  refine ⟨_, hreg, ?_⟩
  have hb4 : ∀ i < 32, (d.b.lo.getD i (.pred false)).bytes = 4 := fun i hi => halfB_bytes (hh i hi)
  have := k.isLt
  simp only [Value.bytes, hb4 _ (by omega : 4 * k.val < 32),
    hb4 _ (by omega : 4 * k.val + 1 < 32), hb4 _ (by omega : 4 * k.val + 2 < 32),
    hb4 _ (by omega : 4 * k.val + 3 < 32)]

/-- **The row-maximum store's payload**: a four-byte word. -/
theorem pay_mst (c : WCtx L g sc l d e) (hs : d.c.site = .mst) {t : TState}
    (hF : Holds t.regs (dF L d)) : ∃ v, t.regs 1109 = some v ∧ v.bytes = 4 := by
  have hp : e.pc = 566 := by rw [c.hpc, hs]; rfl
  obtain ⟨w', hw', -, hlo, hhi, hmw, hpw, -⟩ := c.canon (by omega) (by omega)
  obtain ⟨hm, hl, hmx⟩ := c.carry (by rw [hs]; rfl) (by rw [hs]; rfl)
  rw [dF_site c hs (by simp [innerSite, onChain, isStart])] at hF
  let w : W0Words :=
    { lo := w'.lo, hi := d.b.hi, mw := d.b.mw, pw := d.b.pw, pm := w'.pm, vt := d.b.vt }
  have hw : W0Ok sc w := by
    refine ⟨hw'.scale, ?_, ?_, hw'.loLen, hw'.lo, ?_, ?_, hw'.pm⟩
    · simpa [w, hhi] using hw'.hiLen
    · simpa [w, hhi] using hw'.hi
    · simpa [w, hmw (by omega)] using hw'.mask
    · intro k hk
      simpa [w, hpw k hk (by omega)] using hw'.peer k hk
  have hmem : 1109 ∈ (wF (scX L) .mst d.b).map Prod.fst := by
    show 1109 ∈ (f_mst (scX L) d.b.m d.b.l d.b.mx d.b.sk d.b.lo d.b.hi d.b.mw (d.b.pw 0)
      (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.b.pw 6) (d.b.pw 7)).map Prod.fst
    unfold f_mst
    rw [List.map_append]
    exact List.mem_append_left _ (by simp only [rmax_facts2, List.map_cons, List.map_nil]; decide)
  have hreg := Wg0.Data.holds_of_mem hF hmem
  refine ⟨_, hreg, ?_⟩
  have h := w0_block_mst_has hw c.hx (b := d.b) rfl rfl (fun _ => rfl) hm hl hmx
  have e1 : lookupD (wF (scX L) .mst d.b) 1109 = blkMst (scX L) d.b 1109 := rfl
  rw [e1]
  rcases h with ⟨h1, -⟩ | h
  · exact h1.1
  · rw [h]; rfl

/-- **The vote's payload**: a predicate. -/
theorem pay_vote (c : WCtx L g sc l d e) (hs : d.c.site = .vote) {t : TState}
    (hF : Holds t.regs (dF L d)) : ∃ p, t.regs 109 = some (.pred p) := by
  have hp : e.pc = 578 := by rw [c.hpc, hs]; rfl
  obtain ⟨w, hw, hb⟩ := c.blkIs (by omega) (by omega)
  obtain ⟨hm, hl, hmx⟩ := c.carry (by rw [hs]; rfl) (by rw [hs]; rfl)
  rw [dF_site c hs (by simp [innerSite, onChain, isStart])] at hF
  have hmem : 109 ∈ (wF (scX L) .vote d.b).map Prod.fst := by
    show 109 ∈ (f_vote (scX L) d.b.m d.b.l d.b.mx d.b.sk d.b.lo d.b.hi d.b.mw (d.b.pw 0)
      (d.b.pw 1) (d.b.pw 2) (d.b.pw 3) (d.b.pw 4) (d.b.pw 5) (d.b.pw 6) (d.b.pw 7)
      d.b.pm).map Prod.fst
    unfold f_vote
    rw [List.map_append]
    exact List.mem_append_left _ (by simp only [mld_facts1, List.map_cons, List.map_nil]; decide)
  have hreg := Wg0.Data.holds_of_mem hF hmem
  have hv := w0_vote_pred hw c.hx hb.hi hb.mw hb.pw hb.pm hm hl hmx
  exact ⟨_, by rw [← hv]; exact hreg⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen
  PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {L : Launch} {g : Nat} {sc : ℝ} {l : List Event} {d : D} {e : Event}

theorem bf16Pair_bytes (x y : ℝ) : (Assumptions.bf16Pair x y).bytes = 4 := by
  simp [Assumptions.bf16Pair, Value.bytes, FloatFmt.bytes]

/-- The probability words' registers are facts of the store's site. -/
theorem ost_key_mem (x : BitVec 64) (b : Blk) {t : Nat} (ht : t < 16) :
    1115 + 3 * t ∈ (f_ost x b.m b.l b.mx b.sk b.lo b.hi b.mw (b.pw 0) (b.pw 1) (b.pw 2) (b.pw 3)
      (b.pw 4) (b.pw 5) (b.pw 6) (b.pw 7) b.pm b.vt).map Prod.fst := by
  unfold f_ost
  rw [List.map_append]
  refine List.mem_append_left _ ?_
  simp only [pw_facts4, List.map_cons, List.map_nil]
  interval_cases t <;> decide

/-- **The probability store's payload**: four-byte words. -/
theorem pay_ost (c : WCtx L g sc l d e) (k : Fin 4) (hs : d.c.site = .ost k) {t : TState}
    (hF : Holds t.regs (dF L d)) :
    ∀ i < 4, ∃ v, t.regs (1115 + 12 * k.val + 3 * i) = some v ∧ v.bytes = 4 := by
  intro i hi
  have hp : e.pc = 704 + k.val := by rw [c.hpc, hs]; rfl
  have hk := k.isLt
  obtain ⟨w, hw, hb⟩ := c.blkIs (by omega) (by omega)
  obtain ⟨hm, hl, hmx⟩ := c.carry (by rw [hs]; rfl) (by rw [hs]; rfl)
  rw [dF_site c hs (by simp [innerSite, onChain, isStart])] at hF
  have hmem := ost_key_mem (scX L) d.b (t := 4 * k.val + i) (by omega)
  have hreg := Wg0.Data.holds_of_mem hF (by simpa [wF, wcls, wFc] using hmem)
  have hr : 1115 + 12 * k.val + 3 * i = 1115 + 3 * (4 * k.val + i) := by ring
  refine ⟨_, by rw [hr]; exact hreg, ?_⟩
  obtain ⟨-, -, h3, -⟩ := w0_block hw c.hx hb hm hl hmx
  have h := h3 (4 * k.val + i) (by omega)
  have e1 : lookupD (wF (scX L) (.ost k) d.b) (1115 + 3 * (4 * k.val + i)) =
      blkOst (scX L) d.b (1115 + 3 * (4 * k.val + i)) := rfl
  rw [e1, h]
  exact bf16Pair_bytes _ _

/-- **The Tensor Memory store's payload**: four-byte numbers. -/
theorem pay_rst (c : WCtx L g sc l d e) (k : Fin 4) (hs : d.c.site = .rst k) {t : TState}
    (hF : Holds t.regs (dF L d)) :
    ∀ j < 64, ∃ v, t.regs (1264 + 129 * k.val + j) = some v ∧ v.bytes = 4 := by
  intro j hj
  have hp : e.pc = [814, 915, 1016, 1117].getD k.val 0 := by rw [c.hpc, hs]; rfl
  have hk := k.isLt
  have hb1 : 572 < e.pc ∧ e.pc < 1122 := by rw [hp]; fin_cases k <;> simp
  obtain ⟨w, hw, hb⟩ := c.blkIs hb1.1 hb1.2
  obtain ⟨hm, hl, hmx⟩ := c.carry (by rw [hs]; rfl) (by rw [hs]; rfl)
  obtain ⟨ho, hO⟩ := c.accOk (c.hld.acc (by rw [hp]; fin_cases k <;> simp))
  rw [dF_site c hs (by simp [innerSite, onChain, isStart])] at hF
  obtain ⟨y, s, hfacts, -, -⟩ := rst_facts c.hx hb (fun _ => hw) hm hl hmx k ho hO
  rw [hfacts] at hF
  have hmem : (1264 + 129 * k.val + j, Value.float .f32 (y j * s)) ∈
      mulFacts (1264 + 129 * k.val) y s 64 ++ wF (scX L) (.rld k) d.b := by
    refine List.mem_append_left _ ?_
    simp only [mulFacts, List.mem_map, List.mem_range]
    exact ⟨j, hj, rfl⟩
  exact ⟨_, holds_mem hF hmem, by simp [Value.bytes, FloatFmt.bytes]⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen
  PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {L : Launch} {g : Nat} {sc : ℝ} {l : List Event} {d : D} {e : Event}

/-- **The row-sum store's payload**: a four-byte word. -/
theorem pay_est (c : WCtx L g sc l d e) (hs : d.c.site = .est) {t : TState}
    (hF : Holds t.regs (dF L d)) : ∃ v, t.regs 1727 = some v ∧ v.bytes = 4 := by
  obtain ⟨hm, hl, hmx⟩ := c.carry (by rw [hs]; rfl) (by rw [hs]; rfl)
  rw [dF_site c hs (by simp [innerSite, onChain, isStart])] at hF
  change Holds t.regs (f_exit (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk))) at hF
  have hmem : 1727 ∈ (f_exit (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk))).map
      Prod.fst := by
    unfold f_exit
    rw [List.map_append]
    refine List.mem_append_left _ ?_
    simp only [Gen.e1_facts1, List.map_cons, List.map_nil]
    decide
  have hreg := Wg0.Data.holds_of_mem hF hmem
  have hw1 := (w0e_e1 (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk)) (r := _)
    (m := (w0Carry sc (w0Fin l).1).1) (l := (w0Carry sc (w0Fin l).1).2)
    (by simpa [lookupD, f_car, List.lookup] using hmx)
    (by simpa [lookupD, f_car, List.lookup] using hm)
    (by simpa [lookupD, f_car, List.lookup] using hl)).2
  refine ⟨_, hreg, ?_⟩
  unfold f_exit
  rw [lk_head_mem (by simp only [Gen.e1_facts1, List.map_cons, List.map_nil]; decide)]
  exact hw1.1.1

/-- **The log-sum-exp store's payload**: a four-byte word. -/
theorem pay_lse (c : WCtx L g sc l d e) (hs : d.c.site = .lse) {t : TState}
    (hF : Holds t.regs (dF L d)) : ∃ v, t.regs 1733 = some v ∧ v.bytes = 4 := by
  have hp : e.pc = 1178 := by rw [c.hpc, hs]; rfl
  obtain ⟨hm, hl, hmx⟩ := c.carry (by rw [hs]; rfl) (by rw [hs]; rfl)
  obtain ⟨p, hp0, hrd, -⟩ := c.rowSum (c.hld.rowSum (by simp [hp]))
  rw [dF_site c hs (by simp [innerSite, onChain, isStart])] at hF
  change Holds t.regs (f_lse (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk)) d.b.pe) at hF
  have hmem : 1733 ∈ (f_lse (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk)) d.b.pe).map
      Prod.fst := by
    unfold f_lse
    rw [List.map_append]
    refine List.mem_append_left _ ?_
    simp only [Gen.e4_facts1, List.map_cons, List.map_nil]
    decide
  have hreg := Wg0.Data.holds_of_mem hF hmem
  have hw0 := w0e_lse (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk)) d.b.pe (r := _)
    (m := (w0Carry sc (w0Fin l).1).1) (l := (w0Carry sc (w0Fin l).1).2) (p := p)
    (by simpa [lookupD, f_car, List.lookup] using hmx)
    (by simpa [lookupD, f_car, List.lookup] using hm)
    (by simpa [lookupD, f_car, List.lookup] using hl) hrd (w0Carry_l_nonneg _ _) hp0
  rw [hw0] at hreg
  refine ⟨_, hreg, ?_⟩
  unfold w0LseV
  split_ifs <;> simp [Value.bytes, FloatFmt.bytes]

/-- **The staging store's payload**: four-byte words. -/
theorem pay_ost2 (c : WCtx L g sc l d e) (a : Fin 4) (k : Fin 8) (hs : d.c.site = .ost2 a k)
    {t : TState} (hF : Holds t.regs (dF L d)) :
    ∀ i < 4, ∃ v, t.regs (eStart a + 3 * (4 * k.val + i)) = some v ∧ v.bytes = 4 := by
  intro i hi
  have hp : e.pc = ost2Base a + k.val := by rw [c.hpc, hs]; rfl
  have hk := k.isLt
  obtain ⟨hm, hl, hmx⟩ := c.carry (by rw [hs]; rfl) (by rw [hs]; rfl)
  obtain ⟨sk, hsk⟩ := c.sink
  obtain ⟨p, hp0, hrd, hrp⟩ := c.rowSum (c.hld.rowSum (by
    rw [hp]; fin_cases a <;> fin_cases k <;> simp [ost2Base]))
  obtain ⟨ho, O, hO⟩ := c.acc (c.hld.acc (by
    rw [hp]; fin_cases a <;> fin_cases k <;> simp [ost2Base]))
  rw [dF_site c hs (by simp [innerSite, onChain, isStart])] at hF
  change Holds t.regs (f_os a.val (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk)) d.b.pe
    d.b.o) at hF
  have hmem : eStart a + 3 * (4 * k.val + i) ∈ (f_os a.val (lookupD (f_car (scX L) d.b.m d.b.l
      d.b.mx d.b.sk)) d.b.pe d.b.o).map Prod.fst := by
    unfold f_os
    rw [List.map_append]
    exact List.mem_append_left _ (es_out_key a _ (by omega))
  have hreg := Wg0.Data.holds_of_mem hF hmem
  have hw := w0e_os_word a (scX L) d.b.m d.b.l d.b.mx d.b.sk d.b.pe d.b.o hm hl hmx hsk hrd
    (w0Carry_l_nonneg _ _) hp0 hrp ho hO (4 * k.val + i) (by omega)
  rw [hw] at hreg
  exact ⟨_, hreg, bf16Pair_bytes _ _⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
