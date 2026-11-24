-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionAll
public import Lemmas.Flow.Pointer
public import Lemmas.Flow.Swizzle
public import Lemmas.Flow.SignedBits

@[expose] public section

/-! # The correction warps' setup

After the start barrier the thread computes its warp's index in the group, its row, and the
leader CTA's P-ready barrier of stage 0 (`mapa` of `+144` to rank 0); after the first O-free
arrival there, the barrier of stage 1 (`+152`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- `mapa` of a barrier of the thread's CTA to rank 0: the leader CTA's barrier. -/
theorem run_mapa_lead {P : Params} {L : Launch} {mem0 : Mem0} {g pc d r off : Nat} {t : TState}
    {F : List (Nat × Value)} (hpre : Pre P L mem0) (hg : g < L.threads) (hoff : off < 1024)
    (hc : kernel.code[pc]? = some ⟨none, .addr (.mapa false 32 d (.reg r) (.reg 342))⟩)
    (hat : At t pc F) (h1 : t.regs r = some (b32 (sb L + off)))
    (h2 : t.regs 342 = some (b32 0)) (hpc : 3700 ≤ pc) :
    run kernel asms L g 1 t = some (PTX.next (setReg t d (leadPtr L g off))) := by
  simp only [sb] at h1
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hcl := hpre.cluster
  have hgr := hpre.grid
  have hv := hpre.oneDimLaunch.1
  have hcta : g / L.block < L.grid := cta_lt hg
  have hr : readBits L g t 32 (.reg 342) = .ok (BitVec.ofNat 64 0) := by
    simp only [readBits, readReg, h2, b32, bind, Except.bind, pure, Except.pure,
      truncBits_ofNat (show 0 < 2 ^ 32 by decide) (by decide)]
  rw [run_mapa (rv := BitVec.ofNat 64 0) (loc := ⟨.shared, g / L.block, L.sharedBase + off⟩)
    (peer := ⟨.shared, 2 * (g / L.block / 2), L.sharedBase + off⟩) hc hat
    (readSharedAddress_b32 hg hcta (by omega) h1) hr ?_ asms_localRule_none (segFree hpc)]
  · rfl
  · have hX : 2 * (g / L.block / 2) < L.grid := by omega
    simp only [Launch.mapShared, Launch.peerCta, Launch.oneDim_clusterOfCta hv,
      Launch.oneDim_clusterStart hv, Launch.oneDim_clusterSizeOf hv, hcl, BitVec.toNat_ofNat,
      Nat.zero_mod]
    simp [hcta, hX, Nat.mul_comm]

/-- A selected word (`selp.b32 d, a, b, p`). Irreducible: the evaluation of a segment treats
it as a number. -/
@[irreducible] def selN (c : Bool) (a b : Nat) : Nat := if c then a else b

/-- The selected immediates as words. -/
theorem selV_eq (c : Bool) {a b : Int} {a' b' : Nat} (ha : truncBits 32 (BitVec.ofInt 64 a) =
    BitVec.ofNat 64 a') (hb : truncBits 32 (BitVec.ofInt 64 b) = BitVec.ofNat 64 b') :
    Value.bits 32 (truncBits 32 (BitVec.ofInt 64 (if c then a else b))) = b32 (selN c a' b') := by
  unfold selN
  cases c <;> simp [ha, hb, b32]

/-- Close a fact the signed normal form leaves with a swizzle (`xor` of the row's low bits
into the chunk index), a packed address (`or` of disjoint fields) or a selected immediate:
cases on the selections, then `or` and `xor` as sums, then `omega`. -/
syntax "swz_close" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| swz_close $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      nf_simp [nf_xor, reduceLandMask, toSigned, PTX.compare, decide_eq_decide, ne_eq, stage, selN,
        tmem, $extra,*]
      all_goals (try split_ifs)
      all_goals (try simp only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true,
        Nat.xor_zero] at *)
      all_goals (try simp (disch := omega) only [Nat.mod_eq_of_lt])
      all_goals (try rw [lor_eq_add 12])
      all_goals (try simp (disch := decide) only [xor_mod8, xor_one_mod2, Nat.xor_zero,
        Nat.reduceMod, Nat.reduceDiv, Nat.zero_xor])
      all_goals (try rw [Nat.xor_comm, xor_eq_add 7])
      all_goals (try simp (disch := omega) only [Nat.mod_eq_of_lt])
      all_goals omega))

/-- Evaluate a correction segment to a checkpoint whose facts are `factsX` (`corr_seg` with
the extra values, the masks of the signed normal form and the swizzle). -/
syntax "corr_segx" term:max term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| corr_segx $h $hpre $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      have hbase := ($hpre).sharedRange
      have hal := ($hpre).sharedAlignment
      have hblk := ($hpre).block
      unfold sharedBytes at hbase
      seg_fp $h using
        try simp only [valueX, valueOf, values, chunkValues, loadValues, PTX.Flow.lookupLit,
          Option.getD_some, Option.getD_none, List.lookup_cons, List.lookup_nil, Nat.reduceBEq,
          Bool.cond_true, Bool.cond_false]
        all_goals (try launch_norm $hpre)
        all_goals first
          | with_reducible rfl
          | norm_signed [neg32, sb, kOf, tidOf, warpOf, lnOf, rowOf, hblk,
              $extra,*]
          | swz_close [neg32, sb, kOf, tidOf, warpOf, lnOf, rowOf, hblk,
              $extra,*]
          | seg_close [neg32, sb, kOf, tidOf, warpOf, lnOf, rowOf, hblk,
              $extra,*]))

/-- The value of a register in `factsX`: an extra value, or the table's. -/
theorem mem_factsX {L : Launch} {g pc r : Nat} {d : D} {ex : List (Nat × Value)} {v : Value}
    (hl : r ∈ Flow.live pc) (hv : valueX L g d ex r = v) : (r, v) ∈ factsX L g pc d ex :=
  List.mem_map.mpr ⟨r, hl, by rw [hv]⟩

/-- The start barrier, then the leader's P-ready barrier of stage 0 and its first O-free
arrival. -/
theorem step_bar0 {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {d : D} {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hg : g < L.threads)
    (hs : d.site = .bar0) (hi : Inv L g d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl : i = 0 := hi.start (.inr (.inl rfl))
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_3)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.barSyncN _ _ _) from trivial) hf
  have hd : Inv L g ⟨.free 0, 0, tt, aw, a, o⟩ :=
    inv_same (d := ⟨.bar0, 0, tt, aw, a, o⟩) _ hi rfl
      (.inr (.inr ⟨rfl, .inr (.inr ⟨0, rfl⟩)⟩)) (by simp [Site.inTrip])
      (by simp [Site.rescale]) (fun _ => .inr (.inl rfl))
  obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel asms L g 4 (PTX.next t) = some t1 ∧
      At t1 3760 (factsX L g 3760 ⟨.free 0, 0, tt, aw, a, o⟩ [(2705, b32 (sb L + 144))]) := by
    corr_segx (At.next h) hpre
  have hm := run_mapa_lead (d := 620) (off := 144) hpre hg (by decide) Flow.code_3760 ht1
    (holds_mem ht1.2.2.2.2 (mem_factsX (by table_decide) (by simp [valueX])))
    (holds_mem ht1.2.2.2.2 (mem_factsX (by table_decide) (by
      simp [valueX, valueOf, values, chunkValues, loadValues, PTX.Flow.lookupLit])))
    (by decide)
  have ht2 := At.set (r := 620) (v := leadPtr L g 144) ht1
    (not_mem_factsFrom (show 620 ∉ Flow.live 3760 by table_decide))
  obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel asms L g 1 (PTX.next (setReg t1 620 (leadPtr L g 144)))
      = some t3 ∧ At t3 (Site.free 0).pc (facts L g ⟨.free 0, 0, tt, aw, a, o⟩) := by
    corr_segx ht2 hpre
  exact step_of_run (by simp [next]) hd rfl ⟨_, t3, run_comp hr1 (run_comp hm hr3), ht3⟩

/-- Stage 0's first O-free arrival, then the leader's P-ready barrier of stage 1. -/
theorem step_free0 {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {d : D} {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hg : g < L.threads)
    (hs : d.site = .free 0) (hi : Inv L g d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl : i = 0 := hi.start (.inr (.inr ⟨0, rfl⟩))
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_14)
  obtain rfl := fires_next (show AdvancesOp (.mbarArrive _ _ _ _ _ _ _ none) from trivial) hf
  have hd : Inv L g ⟨.free 1, 0, tt, aw, a, o⟩ :=
    inv_same (d := ⟨.free 0, 0, tt, aw, a, o⟩) _ hi rfl
      (.inr (.inr ⟨rfl, .inr (.inr ⟨1, rfl⟩)⟩))
      (by simp [Site.inTrip]) (by simp [Site.rescale]) (fun _ => .inr (.inr ⟨0, rfl⟩))
  obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel asms L g 1 (PTX.next t) = some t1 ∧
      At t1 3764 (factsX L g 3764 ⟨.free 1, 0, tt, aw, a, o⟩ [(2706, b32 (sb L + 152))]) := by
    corr_segx (At.next h) hpre
  have hm := run_mapa_lead (d := 621) (off := 152) hpre hg (by decide) Flow.code_3764 ht1
    (holds_mem ht1.2.2.2.2 (mem_factsX (by table_decide) (by simp [valueX])))
    (holds_mem ht1.2.2.2.2 (mem_factsX (by table_decide) (by
      simp [valueX, valueOf, values, chunkValues, loadValues, PTX.Flow.lookupLit])))
    (by decide)
  have ht2 := At.set (r := 621) (v := leadPtr L g 152) ht1
    (not_mem_factsFrom (show 621 ∉ Flow.live 3764 by table_decide))
  obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel asms L g 0 (PTX.next (setReg t1 621 (leadPtr L g 152)))
      = some t3 ∧ At t3 (Site.free 1).pc (facts L g ⟨.free 1, 0, tt, aw, a, o⟩) := by
    corr_segx ht2 hpre
  exact step_of_run (by simp [next]) hd rfl ⟨_, t3, run_comp hr1 (run_comp hm hr3), ht3⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
