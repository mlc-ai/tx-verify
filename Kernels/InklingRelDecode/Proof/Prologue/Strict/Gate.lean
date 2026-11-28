-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.Elect
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.PreloadGate
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Divide
import Kernels.InklingRelDecode.Proof.Prologue.Steps.Frame
import Kernels.InklingRelDecode.Proof.Lib.CtlSteps

@[expose] public section

/-! # The strict gate: the proxy fence and the barrier before the preload blocks

From the barrier the lane computes the number of key blocks of its split (two divisions) and
branches to the first preload block or past the blocks. The second division (pc 182) has a
non-negative numerator (the past length of the request) and a positive divisor. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Control Arith32

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

variable (a y p : Nat) (won : Bool) (bcast : Value) (v : Data.Vals)
local notation "GF" pc => dFactsAt Q L g w (dS Site.bar2 a y p won bcast v) pc

theorem gate_a : SegQ kernel Assumptions.all L g (QT proQt) 181 (GF 180) 182 (GF 182) := by
  pro_br seg_gate_numerator

theorem gate_c : SegQ kernel Assumptions.all L g (QT proQt) 183 (GF 183) 185 (GF 185) := by
  pro_br seg_gate_clip

theorem gate_f : SegQ kernel Assumptions.all L g (QT proQt) 185 (GF 185) 189 (GF 189) := by
  pro_br seg_gate_flags

local notation "DD" => Data.dF Q L g (dS Site.bar2 a y p won bcast v)
local notation "VV" => valueOf Q L g w (Data.D.c (dS Site.bar2 a y p won bcast v))

theorem tb_W {n : Nat} (h : n < 2 ^ 32) : truncBits 32 (BitVec.ofNat 64 n) = W n := r32_W h

theorem past_word (r : Nat) (h1 : Q.qStart r ≤ Q.qStart (r + 1)) (h2 : Q.qStart (r + 1) < 2 ^ 32)
    (h3 : Q.qLen r ≤ Q.seqK r) (h4 : Q.seqK r < 2 ^ 32) :
    Lib.word (subValue (b32 (Q.seqK r)) (subValue (b32 (Q.qStart (r + 1))) (b32 (Q.qStart r)))) =
      W (Q.past r) := by
  have hl : Q.qLen r = Q.qStart (r + 1) - Q.qStart r := rfl
  simp only [subValue, Lib.word, b32, Value.regBits, Option.getD_some]
  have h0 : Q.qStart r < 2 ^ 32 := by omega
  have h5 : Q.qLen r < 2 ^ 32 := by omega
  have h6 : Q.past r < 2 ^ 32 := by unfold Params.past; omega
  rw [tb_W h0, tb_W h2, sub32_W h1 h2, tb_W (by omega : Q.qStart (r + 1) - Q.qStart r < 2 ^ 32),
    tb_W h4, ← hl, sub32_W h3 h4]
  exact r32_W h6

/-- **The division of the second iteration count** (pc 182). -/
theorem gate_d (r : Nat) (ha : a = Q.qStart r) (hy : y = Q.qStart (r + 1)) (hq : p = Q.seqK r)
    (h1 : Q.qStart r ≤ Q.qStart (r + 1)) (h2 : Q.qStart (r + 1) < 2 ^ 32)
    (h3 : Q.qLen r ≤ Q.seqK r) (h4 : Q.seqK r + 511 < 2 ^ 31) (hs0 : 0 < Q.splits)
    (hs1 : (L.ctaidOf (g / L.block)).get .x < Q.splits) (hs2 : Q.splits + 2 ^ 24 < 2 ^ 31) :
    SegQ kernel Assumptions.all L g (QT proQt) 182 (GF 182) 183 (GF 183) := by
  refine div_s_piece (dst := 679) (x := 678) (y := 532) Flow.code_182 (by decide +kernel)
    (holds_tab (D := DD) (V := VV) (rs := ctlLive 182) (r := 678) (by decide +kernel))
    (holds_tab (D := DD) (V := VV) (rs := ctlLive 182) (r := 532) (by decide +kernel))
    (fun R h => ?_) ?_ ?_ (by decide +kernel) (by decide +kernel)
  · have h1 := holds_tab_write (D := DD) (V := VV) (rs := ctlLive 182) (rs' := ctlLive 183)
      (dst := 679) (fun q hq => ?_) (by decide +kernel) R h
    · convert h1 using 4
      · simp only [valueOf_plain (by decide +kernel : copyReg 679 = false), registerValue, iters]
        rw [r32_mod32]
      · rfl
    · have := dF_keys_early (L := L) (g := g) (d := dS Site.bar2 a y p won bcast v) rfl q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      omega
  · subst ha hy hq
    change 0 ≤ intOf .s 32 (r32 (add32 (add32 (W Q.splits)
      (not32 (W ((L.ctaidOf (g / L.block)).get Dim.x))))
      (div128 (Lib.word (subValue (b32 (Q.seqK r))
        (subValue (b32 (Q.qStart (r + 1))) (b32 (Q.qStart r))))))))
    rw [past_word r h1 h2 h3 (by omega)]
    exact dividend_nonneg hs1 hs2 (by unfold Params.past; omega)
  · exact divisor_pos hs0 (by omega)

/-- The preload count of the lane at the barrier, from its words. -/
noncomputable abbrev nB : Nat := preloadN Q L g (dS Site.bar2 a y p won bcast v).c

/-- The branch of the gate: to the first preload block, or past the blocks. -/
theorem gate_bra_q : SegQ kernel Assumptions.all L g (QT proQt) 189 (GF 189)
    (if decide (nB (Q := Q) (L := L) (g := g) a y p won bcast v ≠ 0) = true then 190 else 316)
    (GF 189) := by
  refine SegQ.braNot (pick := decide (nB (Q := Q) (L := L) (g := g) a y p won bcast v ≠ 0))
    Flow.code_189 (fun R hR => ?_) (fun t a ha => Lib.bra_rule t a ha) (segFree (by decide))
    (by split <;> decide +kernel)
  have key : 53 ∈ ctlLive 189 := by decide +kernel
  exact holds_tab (D := DD) (V := VV) (rs := ctlLive 189) key R hR

theorem gate_row : SegQ kernel Assumptions.all L g (QT proQt) 190 (GF 189) 192 (GF 192) := by
  refine SegQ.comp (b := 191) (G := GF 191) ?_ ?_
  · pro_br seg_s190
  · pro_br seg_s191

/-- **The gate with preload blocks**: from the barrier to the first block's barrier. -/
theorem gate_ne (r : Nat) (ha : a = Q.qStart r) (hy : y = Q.qStart (r + 1)) (hq : p = Q.seqK r)
    (h1 : Q.qStart r ≤ Q.qStart (r + 1)) (h2 : Q.qStart (r + 1) < 2 ^ 32)
    (h3 : Q.qLen r ≤ Q.seqK r) (h4 : Q.seqK r + 511 < 2 ^ 31) (hs0 : 0 < Q.splits)
    (hs1 : (L.ctaidOf (g / L.block)).get .x < Q.splits) (hs2 : Q.splits + 2 ^ 24 < 2 ^ 31)
    (hn : nB (Q := Q) (L := L) (g := g) a y p won bcast v ≠ 0) :
    SegQ kernel Assumptions.all L g (QT proQt) 181 (GF 180) 192 (GF 192) := by
  have hb := gate_bra_q (Q := Q) (L := L) (g := g) (w := w) a y p won bcast v
  rw [show decide (nB (Q := Q) (L := L) (g := g) a y p won bcast v ≠ 0) = true by simpa using hn]
    at hb
  exact (gate_a a y p won bcast v).comp ((gate_d a y p won bcast v r ha hy hq h1 h2 h3 h4 hs0 hs1
    hs2).comp ((gate_c a y p won bcast v).comp ((gate_f a y p won bcast v).comp
    (hb.comp (gate_row a y p won bcast v)))))

theorem fnc0_next (d : Data.D) (hs : d.c.site = .fnc0) (e : Event) :
    (Data.code Q L g w).next d e = some (some ⟨{ d.c with site := .bar2 }, d.v⟩) := by
  obtain ⟨⟨s, a, b, c, won, bcast⟩, vs⟩ := d
  cases hs
  rfl

/-- **The proxy fence** strictly steps to the barrier. -/
theorem step_fnc0 (d : Data.D) (hs : d.c.site = .fnc0) (e : Event) :
    (Data.code Q L g w).StepForQ (QT proQt) (Wf Q L g) d e := by
  obtain ⟨⟨s, a, b, c, won, bcast⟩, vs⟩ := d
  cases hs
  intro t u ins hat hinv hc hq hw hf
  obtain ⟨hI, hpay⟩ := hinv
  let c0 : Control.D := ⟨.fnc0, a, b, c, won, bcast⟩
  have hi : (Data.code Q L g w).inv ⟨⟨.bar2, a, b, c, won, bcast⟩, vs⟩ :=
    ⟨trivial, payload_next (Q := Q) (L := L) (g := g) (d := c0) (e := ⟨0, .exit⟩)
      (t := ⟨.bar2, a, b, c, won, bcast⟩) rfl hpay (fun j h => by cases h)⟩
  refine Code.advanceQ (C := Data.code Q L g w) (qt := proQt) (ex := [])
    (d := ⟨c0, vs⟩) (dn := ⟨⟨.bar2, a, b, c, won, bcast⟩, vs⟩) Flow.code_179
    (fun h => fires_next (by trivial) h) (fun e => fnc0_next _ rfl e) rfl rfl rfl rfl hi
    (fun _ _ => typed_nil') (by decide +kernel : Code.afterWrites proQt 179 [] [] = true)
    (SegQ.weaken fun R hR => holds_code_mono (w := w) (d := ⟨c0, vs⟩)
      (d' := ⟨⟨.bar2, a, b, c, won, bcast⟩, vs⟩) (dF_early rfl rfl) rfl
      (by decide +kernel : (ctlLive 180).isSublist (ctlLive 179) = true) hR)
    e ins hat ⟨hI, hpay⟩ hc hq hw hf

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
