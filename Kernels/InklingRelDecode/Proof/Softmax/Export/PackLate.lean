-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.LateValues
public import Kernels.InklingRelDecode.Flow.Sites.Part000
public import Lemmas.Flow.OutKinds
import Kernels.InklingRelDecode.Proof.Softmax.Data.PackWin
import Kernels.InklingRelDecode.Proof.Softmax.Data.LaneStop
import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpTyped
import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpFam

/-! # The first pack reads numbers

A state of a lane at a pack of pcs 952 to 998 comes from the state after an event of the code
after the row sum; the exponentials' pairs it holds are numbers (`PkIn`), and the unpacked halves
the pack reads are numbers too (`pack_reads`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow PTX.Assumption Control Data Lib

variable {Q : Params} {L : Launch} {g : Nat}

set_option maxRecDepth 100000

private theorem round_site (s : Site) (h1 : 2234 ≤ s.pc) (h2 : s.pc ≤ 2329) :
    inRound s = true := by
  revert h1 h2
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem code_999 : (match kernel.code[999]? with
    | some ins => ins.guard.isNone && !ins.op.isLocal | none => false) = true := by
  decide +kernel

private theorem pack_a {m : Mem0} {X : Execution} {t : TState}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hS : ∀ k a vals sh, X.get (g, k) = some ⟨Flow.tmemLoad_0, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x)
    (h5 : g % L.block < 128 → ∀ k mode sent b c recv ok,
      X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩ → SK.ni.Has sent ∧ SK.ni.Has recv)
    (lane : g % L.block < 128) (hl : Iface.LaneState L X g t) (h1 : 952 ≤ t.pc) (h2 : t.pc ≤ 998)
    {c : CvtInstr} (hc : kernel.code[t.pc]? = some ⟨none, .cvt c⟩)
    (hpk : Iface.packOp (.cvt c) = true) :
    ∀ r ∈ c.srcs, ∀ a, r = .reg a → ∃ x : EReal, readERealOpnd t .f32 r = some (.ok x) := by
  have hin : inS packWin t.pc = true := by simp only [inS, packWin]; simp; omega
  obtain ⟨k, e, t0, hk, hr1, ⟨s, hes⟩, hev, hin0, hrt, -⟩ :=
    lane_set packWin_fwd packWin_enter packWin_zero hl hin
  have hspc := EventFrame.estep_source_pc hes
  have hpost := post_pc hes
  rcases packWin_events e.pc (by simpa [entryEvents] using hev) with h999 | ⟨e1, e2⟩
  · exfalso
    have h0 : t0.pc = 999 := by
      have : t0.pc = 999 ∨ t0.pc = 1000 := by omega
      rcases this with h | h
      · exact h
      · rw [h] at hin0; simp [inS, packWin] at hin0
    rcases Relation.ReflTransGen.cases_head hrt with rfl | ⟨c1, hc1, -⟩
    · omega
    · obtain ⟨ins, hci, -, hk⟩ := win_cases hc1
      rw [h0] at hci
      have := code_999
      rw [hci] at this
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.not_eq_true'] at this
      rcases hk with ⟨hs, -⟩ | ⟨hl', -⟩
      · simp [this.1] at hs
      · rw [this.2] at hl'; cases hl'
  obtain ⟨ent, y, sp, hsite, hat, hes', typ, ni⟩ := lane_stop hp hX hf hS h5 lane
    hk hr1 (by omega) (by omega)
  have hr : inRound y.c.site = true := round_site _ (by omega) (by omega)
  have hE : ExpIn (xV ent L g y) := by
    have hm : (Kd.s .ni).Has (m0 y) := by
      have : m0 y = y.v.m := by
        simp only [m0]
        have : y.c.site ≠ .bar20 ∧ y.c.site ≠ .tmemSt := by
          constructor <;> intro h <;> rw [h] at hr <;> simp [inRound] at hr
        simp [this.1, this.2]
      rw [this]; exact ni.m
    exact xV_expIn hp typ hm ni.mx
  obtain ⟨-, -, -, -, hreg⟩ := hat
  have hF := atS_xF hreg
  rw [xF_round hr hE] at hF
  have hsp : ∀ r ∈ pkDom, sp.regs r = some (xE ent L g y r) := fun r hr' =>
    holds_mem hF (mem_factsFrom (by simpa using pkDom_xKeys r hr'))
  have ht0 : ∀ r ∈ pkDom, t0.regs r = some (xE ent L g y r) := fun r hr' => by
    obtain ⟨ins, hci, -, -⟩ := EventFrame.estep_event_source hes'
    have spc := EventFrame.estep_source_pc hes'
    have hkp := (packWin_keep e.pc (by simpa [entryEvents] using hev)).resolve_left (by omega)
    rw [spc, hci] at hkp
    have hnw : r ∉ EventFrame.eventWrites ins.op := by
      have := List.all_eq_true.mp hkp r hr'
      simpa using this
    rw [estep_keeps hes' ins hci r hnw]
    exact hsp r hr'
  have hS' : inS [(951, 998)] t.pc = true := by simp only [inS]; simp; omega
  have hS0 : inS [(951, 998)] t0.pc = false := by
    have : t0.pc ≥ 2234 := by omega
    simp only [inS]; simp; omega
  obtain ⟨u, hu1, hu2, hupc, -⟩ := first_entry pk1_enter hrt hS0 hS'
  have huin : inS packWin t0.pc = true := hin0
  obtain ⟨-, hukeep⟩ := win_keep packWin_fwd hu1 huin
  have hufault : u.fault = none := by
    rcases Relation.ReflTransGen.cases_head hu2 with rfl | ⟨c1, hc1, -⟩
    · omega
    · obtain ⟨-, -, hfa, -⟩ := win_cases hc1
      exact hfa
  have hpkE : PkIn (xE ent L g y) := pkIn_of hE
  have hd : ∀ r ∈ pkDom, u.regs r = some ((fun r => (u.regs r).getD (Value.bits 32 0)) r) :=
    fun r hr' => by
      show u.regs r = some ((u.regs r).getD (Value.bits 32 0))
      rw [hukeep r hr', ht0 r hr']; rfl
  have hlen : pk1All.length = 48 := by simp [pk1All, Gen.pk1_items0, Gen.pk1_items1]
  obtain ⟨j, hj, hjpc, hregs⟩ := xItems_pre (V := fun r => (u.regs r).getD (Value.bits 32 0))
    (dom := pkDom) (hupc ▸ pk1_at L g) hufault hd pk1_reads (pk1_req _) pk1_local hu2
    (fun t1 t' e1 e2 e3 => by
      have h1 : inS [(999, 999)] t1.pc = true := by simp only [inS]; simp; omega
      have := (win_keep pk1_after e2 h1).1
      simp only [inS] at this; simp at this; omega) (by omega) (by omega)
  obtain ⟨K', hK'⟩ := Option.isSome_iff_exists.mp (by simpa [kOk] using pk1_kRun)
  refine pack_reads (K := kPair) hK' pk1_fns (fun r => ?_) pk1_sites hj (by omega) hregs hc hpk
  by_cases hr' : 1994 ≤ r ∧ r < 2018
  · have hm : r ∈ pkDom := by
      simp only [pkDom, List.mem_map, List.mem_range]
      exact ⟨r - 1994, by omega, by omega⟩
    have hv : (u.regs r).getD (Value.bits 32 0) = xE ent L g y r := by
      rw [hukeep r hm, ht0 r hm]; rfl
    have hk : kPair r = Kd.pr .fl := by simp [kPair, hr']
    show (kPair r).Has ((u.regs r).getD (Value.bits 32 0))
    rw [hk, hv]
    simpa [ExpTy, hr'] using hpkE.pr r hr'.1 hr'.2
  · simp [kPair, hr', Kd.Has]

private theorem site_999 (s : Site) (h : s.pc = 999) : s = .bar20 := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem pack_b {m : Mem0} {X : Execution} {t : TState}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hS : ∀ k a vals sh, X.get (g, k) = some ⟨Flow.tmemLoad_0, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x)
    (h5 : g % L.block < 128 → ∀ k mode sent b c recv ok,
      X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩ → SK.ni.Has sent ∧ SK.ni.Has recv)
    (lane : g % L.block < 128) (hl : Iface.LaneState L X g t) (h1 : 1000 ≤ t.pc)
    (h2 : t.pc ≤ 1007) {c : CvtInstr} (hc : kernel.code[t.pc]? = some ⟨none, .cvt c⟩)
    (hpk : Iface.packOp (.cvt c) = true) :
    ∀ r ∈ c.srcs, ∀ a, r = .reg a → ∃ x : EReal, readERealOpnd t .f32 r = some (.ok x) := by
  have hin : inS pack2Win t.pc = true := by simp only [inS, pack2Win]; simp; omega
  obtain ⟨k, e, t0, hk, hr1, ⟨s, hes⟩, hev, hin0, hrt, -⟩ :=
    lane_set pack2_fwd pack2_enter pack2_zero hl hin
  have hspc := EventFrame.estep_source_pc hes
  have hpost := post_pc hes
  have h999 : e.pc = 999 := by
    rcases pack2_events e.pc (by simpa [entryEvents] using hev) with h | h | h
    · exact h
    all_goals
      exfalso
      have hq : inS [(1009, 1010)] t0.pc = true := by
        simp only [inS]; simp; simp only [pack2Win, inS] at hin0; simp at hin0; omega
      have := (win_keep pk2_late hrt hq).1
      simp only [inS] at this; simp at this; omega
  obtain ⟨ent, y, sp, hsite, hat, hes', typ, ni⟩ := lane_stop hp hX hf hS h5 lane
    hk hr1 (by omega) (by omega)
  have hy := site_999 _ (hsite.trans h999)
  have hE : ExpIn (xV ent L g y) := by
    have hm : (Kd.s .ni).Has (m0 y) := by
      have : m0 y = y.v.mp := by simp [m0, hy]
      rw [this]; exact ni.mp
    exact xV_expIn hp typ hm ni.mx
  obtain ⟨-, -, -, -, hreg⟩ := hat
  have hF := atS_xF hreg
  rw [xF_bar20 hy hE] at hF
  have hsp : ∀ r ∈ pkS, sp.regs r = some (vP1 (xE ent L g y) r) := fun r hr' =>
    holds_mem hF (mem_factsFrom (pkS_kB20 r hr'))
  have ht0 : ∀ r ∈ pkS, t0.regs r = some (vP1 (xE ent L g y) r) := fun r hr' => by
    obtain ⟨ins, hci, -, -⟩ := EventFrame.estep_event_source hes'
    have spc := EventFrame.estep_source_pc hes'
    have hkp := pack2_keep
    rw [← h999, spc] at hkp
    rw [hci] at hkp
    have hnw : r ∉ EventFrame.eventWrites ins.op := by
      have := List.all_eq_true.mp hkp r hr'
      simpa using this
    rw [estep_keeps hes' ins hci r hnw]
    exact hsp r hr'
  have h0pc : t0.pc = 1000 := by
    simp only [pack2Win, inS] at hin0; simp at hin0; omega
  have hS' : inS [(1000, 1007)] t.pc = true := by simp only [inS]; simp; omega
  have hpkE : PkIn (vP1 (xE ent L g y)) := pkIn_p1 (pkIn_of hE)
  have hd : ∀ r ∈ pkS, t0.regs r = some ((fun r => (t0.regs r).getD (Value.bits 32 0)) r) :=
    fun r hr' => by
      show t0.regs r = some ((t0.regs r).getD (Value.bits 32 0))
      rw [ht0 r hr']; rfl
  have hlen : Gen.pk2_items0.length = 8 := by simp [Gen.pk2_items0]
  obtain ⟨j, hj, hjpc, hregs⟩ : ∃ j < Gen.pk2_items0.length, t.pc = 1000 + j ∧
      ∀ r ∈ xWrites (Gen.pk2_items0.take j) ++ pkS, t.regs r =
        some (xFinal (fun r => (t0.regs r).getD (Value.bits 32 0)) (Gen.pk2_items0.take j) r) := by
    rcases Relation.ReflTransGen.cases_head hrt with rfl | ⟨c1, hc1, -⟩
    · refine ⟨0, by omega, by omega, fun r hr' => ?_⟩
      have hm : r ∈ pkS := by simpa [xWrites] using hr'
      simp only [List.take_zero, xFinal]
      rw [ht0 r hm]; rfl
    · obtain ⟨-, -, hfa, -⟩ := win_cases hc1
      obtain ⟨j, hj, hq, hr⟩ := xItems_pre (V := fun r => (t0.regs r).getD (Value.bits 32 0))
        (dom := pkS) (h0pc ▸ Gen.pk2_at0 L g) hfa hd pk2_reads (pk2_req _) pk2_local hrt
        (fun t1 t' e1 e2 e3 => by
          have h1 : inS [(1008, 1010)] t1.pc = true := by simp only [inS]; simp; omega
          have := (win_keep pk2_after e2 h1).1
          simp only [inS] at this; simp at this; omega) (by omega) (by omega)
      exact ⟨j, hj, by omega, hr⟩
  obtain ⟨K', hK'⟩ := Option.isSome_iff_exists.mp (by simpa [kOk] using pk2_kRun)
  refine pack_reads (K := kSing) hK' pk2_fns (fun r => ?_) pk2_sites hj (by omega) hregs hc hpk
  by_cases hr' : 508 ≤ r ∧ r < 524
  · have hm : r ∈ pkS := by
      simp only [pkS, List.mem_map, List.mem_range]
      exact ⟨r - 508, by omega, by omega⟩
    have hv : (t0.regs r).getD (Value.bits 32 0) = vP1 (xE ent L g y) r := by
      rw [ht0 r hm]; rfl
    have hk : kSing r = Kd.s .fl := by simp [kSing, hr']
    show (kSing r).Has ((t0.regs r).getD (Value.bits 32 0))
    rw [hk, hv]
    simpa [ExpTy, hr'] using hpkE.sg r hr'.1 hr'.2
  · simp [kSing, hr', Kd.Has]

private theorem packPc_scan : scanCode (fun pc ins =>
    !(((decide (574 ≤ pc) && decide (pc < 2331)) || (decide (2560 ≤ pc) && decide (pc < 2853))) &&
      !Assumptions.emuSites.contains pc && Iface.packOp ins.op) ||
      decide ((952 ≤ pc ∧ pc ≤ 998) ∨ (1000 ≤ pc ∧ pc ≤ 1007))) kernel.code 0 = true := by
  decide +kernel

private theorem packPc_range (pc : Nat) (h : Iface.packPc pc = true) :
    (952 ≤ pc ∧ pc ≤ 998) ∨ (1000 ≤ pc ∧ pc ≤ 1007) := by
  cases hc : kernel.code[pc]? with
  | none => simp [Iface.packPc, hc] at h
  | some ins =>
    have := scanCode_get packPc_scan hc
    simp only [Iface.packPc, hc] at h
    rw [Nat.zero_add] at this
    simp only [h, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this
    exact this

/-- **Both sources of a pack `cvt.rn.bf16x2.f32` of the probabilities read as extended reals.** -/
public theorem pack_late {m : Mem0} {X : Execution}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hS : ∀ k a vals sh, X.get (g, k) = some ⟨Flow.tmemLoad_0, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x)
    (h5 : g % L.block < 128 → ∀ k mode sent b c recv ok,
      X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩ → SK.ni.Has sent ∧ SK.ni.Has recv)
    (lane : g % L.block < 128) {t : TState} (hl : Iface.LaneState L X g t)
    (hpc : Iface.packPc t.pc = true) :
    ∀ c, kernel.code[t.pc]? = some ⟨none, .cvt c⟩ → ∀ r ∈ c.srcs, ∀ a, r = .reg a →
      ∃ x : EReal, readERealOpnd t .f32 r = some (.ok x) := by
  intro c hc
  have hpk : Iface.packOp (.cvt c) = true := by
    have h := hpc
    simp only [Iface.packPc, hc, Bool.and_eq_true] at h
    exact h.2
  rcases packPc_range _ hpc with ⟨a1, a2⟩ | ⟨a1, a2⟩
  · exact pack_a hp hX hf hS h5 lane hl a1 a2 hc hpk
  · exact pack_b hp hX hf hS h5 lane hl a1 a2 hc hpk

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
