-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.LateValues
public import Kernels.InklingRelDecode.Flow.Sites.Part000
import Kernels.InklingRelDecode.Proof.Softmax.Data.WordsTy
import Kernels.InklingRelDecode.Proof.Softmax.Data.LaneStop

/-! # The unpacks of the bias packs read words of two halves

The first window (pcs 1299 to 1838) is entered after the wait of the score load only, and writes
none of the 32 pack registers. At that wait the machine's facts hold the packs of the round's bias
words, which are words of two halves (`packV_word32`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Assumption PTX.Flow.TyG Control Data Lib

variable {Q : Params} {L : Launch} {g : Nat}

set_option maxRecDepth 100000

/-- The first window. -/
private def cWin : List (Nat × Nat) := [(1299, 1838)]
/-- The registers of the packs. -/
private def cRegs : List Nat := (List.range 32).map (1916 + ·)

private theorem cw_fwd : fwdOk cWin cRegs = true := by decide +kernel
private theorem cw_enter : enterOk cWin 0 = true := by decide +kernel
private theorem cw_zero : inS cWin 0 = false := by decide +kernel
private theorem cw_events : ∀ q ∈ entryEvents cWin, q = 1298 ∨ q = 1838 := by decide +kernel
private theorem keepWait : (match kernel.code[1298]? with
    | some ins => cRegs.all fun r => !(EventFrame.eventWrites ins.op).contains r
    | none => true) = true := by
  decide +kernel

private theorem site_1298 (s : Site) (h : s.pc = 1298) : s = .waitLd := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

/-- **The packs hold words of two halves** at every state of the first window. -/
private theorem c_win {m : Mem0} {X : Execution} {t : TState}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hS : ∀ k a vals sh, X.get (g, k) = some ⟨Flow.tmemLoad_0, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x)
    (h5 : g % L.block < 128 → ∀ k mode sent b c recv ok,
      X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩ → SK.ni.Has sent ∧ SK.ni.Has recv)
    (lane : g % L.block < 128) (hl : Iface.LaneState L X g t) (h1 : 1299 ≤ t.pc)
    (h2 : t.pc ≤ 1429) : ∀ r, 1916 ≤ r → r < 1948 → ∃ v, t.regs r = some v ∧ Word32 v := by
  intro r hr1 hr2
  have hin : inS cWin t.pc = true := by simp only [inS, cWin]; simp; omega
  obtain ⟨k, e, t0, hk, hr1', ⟨s, hes⟩, hev, hin0, hrt, hkeep⟩ :=
    lane_set cw_fwd cw_enter cw_zero hl hin
  have hpost := post_pc hes
  have hspc := EventFrame.estep_source_pc hes
  have h98 : e.pc = 1298 := by
    rcases cw_events e.pc hev with h | h
    · exact h
    · exfalso
      simp only [inS, cWin] at hin0; simp at hin0
      have h38 : t0.pc = 1838 := by omega
      rcases Relation.ReflTransGen.cases_head hrt with h0 | ⟨c, hc, -⟩
      · subst h0; omega
      · exact no_tau_evAt (by rw [h38]; decide +kernel) hc
  obtain ⟨ent, y, sp, hsite, hat, hes', typ, ni⟩ :=
    lane_stop hp hX hf hS h5 lane hk hr1' (by omega) (by omega)
  have hy : y.c.site = .waitLd := site_1298 _ (hsite.trans h98)
  obtain ⟨ins, hci, -, -⟩ := EventFrame.estep_event_source hes'
  have hsp : sp.pc = 1298 := by have := EventFrame.estep_source_pc hes'; omega
  have hnw : ∀ r ∈ cRegs, r ∉ EventFrame.eventWrites ins.op := by
    have := keepWait
    rw [hsp] at hci
    rw [hci] at this
    intro r hr
    simpa using List.all_eq_true.mp this r hr
  have hm : r - 1916 < 32 := by omega
  have hrm : r ∈ cRegs := by
    simp only [cRegs, List.mem_map, List.mem_range]
    exact ⟨r - 1916, hm, by omega⟩
  have hmem : (r, packV (y.v.cur (2 * (r - 1916))) (y.v.cur (2 * (r - 1916) + 1))) ∈ wF y := by
    simp only [wF, hy, wFS, wP, ↓reduceIte, List.mem_append, packF, List.mem_map, List.mem_range]
    exact .inl ⟨r - 1916, hm, by simp only [Prod.mk.injEq, and_true]; omega⟩
  have hv := holds_mem (atS_wFat hat) hmem
  refine ⟨packV (y.v.cur (2 * (r - 1916))) (y.v.cur (2 * (r - 1916) + 1)), ?_,
    packV_word32 (typ.cur _) (typ.cur _)⟩
  rw [hkeep r hrm, estep_keeps hes' ins hci r (hnw r hrm)]
  exact hv

/-- A state of the first window after its first position comes from a state of the lane by one
local step. -/
private theorem c_pred {X : Execution} {t : TState} (hl : Iface.LaneState L X g t)
    (h1 : 1300 ≤ t.pc) (h2 : t.pc ≤ 1429) :
    ∃ b, Iface.LaneState L X g b ∧ Tau kernel Assumptions.all L g b t := by
  have hin : inS cWin t.pc = true := by simp only [inS, cWin]; simp; omega
  obtain ⟨k, e, t0, hk, hr1, ⟨s, hes⟩, hev, hin0, hrt, -⟩ := lane_set cw_fwd cw_enter cw_zero hl hin
  have hpost := post_pc hes
  have hspc := EventFrame.estep_source_pc hes
  have h98 : e.pc = 1298 := by
    rcases cw_events e.pc hev with h | h
    · exact h
    · exfalso
      simp only [inS, cWin] at hin0; simp at hin0
      have h38 : t0.pc = 1838 := by omega
      rcases Relation.ReflTransGen.cases_head hrt with h0 | ⟨c, hc, -⟩
      · subst h0; omega
      · exact no_tau_evAt (by rw [h38]; decide +kernel) hc
  rcases Relation.ReflTransGen.cases_tail hrt with h | ⟨b, hb, hbt⟩
  · subst h; omega
  · exact ⟨b, ⟨k + 1, t0, hr1, hb⟩, hbt⟩

/-- The unpack, cvt, cvt triple of a pair of halves. -/
private def tripleOk (m : Nat) : Bool :=
  match kernel.code[1303 + 4 * m]?, kernel.code[1304 + 4 * m]?, kernel.code[1305 + 4 * m]? with
  | some ⟨none, .move ⟨.unpack, .int .b 32, [some lo, some hi], [.reg a]⟩⟩,
    some ⟨none, .cvt c1⟩, some ⟨none, .cvt c2⟩ =>
    lo == 397 + 2 * m && hi == 398 + 2 * m && a == 1947 - m && c1.srcs == [.reg hi] &&
      c2.srcs == [.reg lo] && !(writesRegs (.cvt c1)).contains lo &&
      !(writesRegs (.cvt c1)).contains hi && Iface.halfSrcs (.cvt c1) == some [.reg hi] &&
      Iface.halfSrcs (.cvt c2) == some [.reg lo]
  | _, _, _ => false

private theorem triple_all : (List.range 32).all tripleOk = true := by decide +kernel

private theorem pred_scan : scanCode (fun pc ins =>
    ((Lib.succs pc ins.op) ++ (if ins.guard.isSome then [pc + 1] else [])).all fun q =>
      !(decide (1304 ≤ q ∧ q ≤ 1429) && ((q - 1303) % 4 == 1 || (q - 1303) % 4 == 2)) ||
        (pc + 1 == q)) kernel.code 0 = true := by
  decide +kernel

private theorem pred_pc {b t : TState} (h : Tau kernel Assumptions.all L g b t)
    (hq : 1304 ≤ t.pc ∧ t.pc ≤ 1429) (hm : (t.pc - 1303) % 4 = 1 ∨ (t.pc - 1303) % 4 = 2) :
    b.pc + 1 = t.pc := by
  obtain ⟨ins, hc, -, hk⟩ := win_cases h
  have hsc := scanCode_get pred_scan hc
  rw [Nat.zero_add] at hsc
  rcases hk with ⟨-, hp, -⟩ | ⟨-, hp, -⟩
  · omega
  · have := List.all_eq_true.mp hsc t.pc (by simp [hp])
    simp at this
    omega

private theorem contains_false {l : List Nat} {a : Nat} (h : l.contains a = false) : a ∉ l :=
  fun hm => by
    have := List.contains_iff_mem.mpr hm
    rw [h] at this
    cases this

private theorem triple_spec {m : Nat} (hm : m < 32) : ∃ lo hi a c1 c2,
    kernel.code[1303 + 4 * m]? =
      some ⟨none, .move ⟨.unpack, .int .b 32, [some lo, some hi], [.reg a]⟩⟩ ∧
    kernel.code[1304 + 4 * m]? = some ⟨none, .cvt c1⟩ ∧
    kernel.code[1305 + 4 * m]? = some ⟨none, .cvt c2⟩ ∧ lo = 397 + 2 * m ∧ hi = 398 + 2 * m ∧
    a = 1947 - m ∧ lo ∉ writesRegs (.cvt c1) ∧ hi ∉ writesRegs (.cvt c1) ∧
    Iface.halfSrcs (.cvt c1) = some [.reg hi] ∧ Iface.halfSrcs (.cvt c2) = some [.reg lo] := by
  have h := List.all_eq_true.mp triple_all m (List.mem_range.mpr hm)
  unfold tripleOk at h
  split at h
  · rename_i lo hi a c1 c2 e0 e1 e2
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, -⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
    exact ⟨lo, hi, a, c1, c2, e0, e1, e2, h1, h2, h3,
      contains_false h6,
      contains_false h7, h8, h9⟩
  · cases h

/-- The steps of the unpack, as a local step. -/
private theorem tau_exec {b t u : TState} {op : Op} (hc : kernel.code[b.pc]? = some ⟨none, op⟩)
    (hl : op.isLocal = true) (hx : execLocalA Assumptions.all L g b op = .ok u)
    (h : Tau kernel Assumptions.all L g b t) : t = u := by
  unfold Tau out at h
  cases hf : b.fault with
  | some f => simp [hf] at h
  | none =>
    simp only [hf, hc, guardHolds, hl, hx, pure, Except.pure, ↓reduceIte, Out.tau.injEq] at h
    exact h.symm

private theorem split_half16 {v : Value} (h : Word32 v) :
    Half16 (splitValue 32 v).1 ∧ Half16 (splitValue 32 v).2 := by
  rcases h with ⟨x, rfl⟩ | ⟨lo, hi, rfl, h1, h2⟩
  · exact ⟨.inl ⟨_, rfl⟩, .inl ⟨_, rfl⟩⟩
  · exact ⟨h1, h2⟩

/-- **The local step of an unpack of a word of two halves** gives its two halves. -/
private theorem unpack_tau {b t : TState} {lo hi a : Nat} (hne : lo ≠ hi)
    (hc : kernel.code[b.pc]? = some ⟨none, (YItem.unpack 32 lo hi a).op⟩)
    (hint : intPc b.pc = true) (hv : ∃ v, b.regs a = some v ∧ Word32 v)
    (h : Tau kernel Assumptions.all L g b t) :
    ∃ v, Word32 v ∧ t.regs lo = some (splitValue 32 v).1 ∧
      t.regs hi = some (splitValue 32 v).2 := by
  obtain ⟨v, hv, hw⟩ := hv
  obtain ⟨hb, h1, h2⟩ := split_word hw
  have hR := rule_unpack (L := L) (g := g) (lo := lo) (hi := hi) (a := a) (w := 32) b.pc hint
    rfl b rfl
  have hVa : (fun r => (b.regs r).getD dflt) a = v := by simp [hv]
  have hx := (YItem.exec (YItem.unpack 32 lo hi a) (V := fun r => (b.regs r).getD dflt)
    (smSegFree hint) hR (fun r hr => by
      simp only [YItem.reads, List.mem_singleton] at hr
      subst hr
      simp [hv]) rfl).1 (by simpa only [YItem.cond, hVa] using ⟨hb, h1, h2⟩)
  have ht := tau_exec hc rfl hx h
  subst ht
  refine ⟨v, hw, ?_, ?_⟩
  · simp [YItem.post, YItem.vals, setReg, PTX.next, hv, Function.update_of_ne hne]
  · simp [YItem.post, YItem.vals, setReg, PTX.next, hv]

private theorem emu_c : ((List.range' 1299 140).all fun pc =>
    !Assumptions.emuSites.contains pc) = true := by
  decide +kernel

private theorem mod3_scan : scanCode (fun pc ins =>
    decide (pc < 1303 ∨ 1429 < pc ∨ (pc - 1303) % 4 ≠ 3) || (Iface.halfSrcs ins.op).isNone)
    kernel.code 0 = true := by
  decide +kernel

/-- **The halves an unpack wrote are halves** (at the first cvt after it). -/
private theorem c_halves {m : Mem0} {X : Execution} {t : TState}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hS : ∀ k a vals sh, X.get (g, k) = some ⟨Flow.tmemLoad_0, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x)
    (h5 : g % L.block < 128 → ∀ k mode sent b c recv ok,
      X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩ → SK.ni.Has sent ∧ SK.ni.Has recv)
    (lane : g % L.block < 128) (hl : Iface.LaneState L X g t) {n : Nat} (hn : n < 32)
    (hpc : t.pc = 1304 + 4 * n) :
    (∃ v, t.regs (397 + 2 * n) = some v ∧ Half16 v) ∧
      (∃ v, t.regs (398 + 2 * n) = some v ∧ Half16 v) := by
  obtain ⟨b, hb, htb⟩ := c_pred hl (by omega) (by omega)
  have hbpc : b.pc + 1 = t.pc := pred_pc htb ⟨by omega, by omega⟩ (Or.inl (by omega))
  obtain ⟨lo, hi, a, c1, c2, e0, e1, e2, hlo, hhi, ha, -, -, -, -⟩ := triple_spec hn
  have hbc : b.pc = 1303 + 4 * n := by omega
  have hcb : kernel.code[b.pc]? = some ⟨none, (YItem.unpack 32 lo hi a).op⟩ := by
    rw [hbc]; exact e0
  have hwin := c_win hp hX hf hS h5 lane hb (by omega) (by omega) a (by omega) (by omega)
  obtain ⟨v, hw, hlo', hhi'⟩ := unpack_tau (by omega) hcb (by simp [intPc]; omega) hwin htb
  obtain ⟨s1, s2⟩ := split_half16 hw
  subst hlo hhi
  exact ⟨⟨_, hlo', s1⟩, ⟨_, hhi', s2⟩⟩

/-- **The registers an unpack of a bias pack and the two widenings after it read hold a word of
two halves, resp. halves** (pcs 1303 to 1429). -/
public theorem half_c {m : Mem0} {X : Execution} {t : TState}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hS : ∀ k a vals sh, X.get (g, k) = some ⟨Flow.tmemLoad_0, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x)
    (h5 : g % L.block < 128 → ∀ k mode sent b c recv ok,
      X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩ → SK.ni.Has sent ∧ SK.ni.Has recv)
    (lane : g % L.block < 128) (hl : Iface.LaneState L X g t) (h1 : 1303 ≤ t.pc) (h2 : t.pc ≤ 1429)
    {i : Instr} (hc : kernel.code[t.pc]? = some i) {srcs : List Opnd}
    (hs : Iface.halfSrcs i.op = some srcs) {r : Nat} (hr : .reg r ∈ srcs) :
    ∃ v, t.regs r = some v ∧ TyG.halfSrcOk i.op v := by
  obtain ⟨n, d, hnd, hd⟩ : ∃ n d, t.pc = 1303 + 4 * n + d ∧ d < 4 :=
    ⟨(t.pc - 1303) / 4, (t.pc - 1303) % 4, by omega, by omega⟩
  have hn : n < 32 := by omega
  obtain ⟨lo, hi, a, c1, c2, e0, e1, e2, hlo, hhi, ha, hw1, hw2, hs1, hs2⟩ := triple_spec hn
  rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3) with rfl | rfl | rfl | rfl
  · rw [show t.pc = 1303 + 4 * n by omega, e0] at hc
    obtain rfl := Option.some.inj hc
    have hsrc : Iface.halfSrcs (.move ⟨.unpack, .int .b 32, [some lo, some hi], [.reg a]⟩) =
        some [.reg a] := by simp [Iface.halfSrcs, DType.width]
    rw [hsrc] at hs
    obtain rfl := Option.some.inj hs
    have hra : r = a := by simpa using hr
    rw [hra]
    exact c_win hp hX hf hS h5 lane hl (by omega) (by omega) a (by omega) (by omega)
  · rw [show t.pc = 1304 + 4 * n by omega, e1] at hc
    obtain rfl := Option.some.inj hc
    rw [hs1] at hs
    obtain rfl := Option.some.inj hs
    have hra : r = hi := by simpa using hr
    rw [hra, hhi]
    exact (c_halves hp hX hf hS h5 lane hl hn (by omega)).2
  · rw [show t.pc = 1305 + 4 * n by omega, e2] at hc
    obtain rfl := Option.some.inj hc
    rw [hs2] at hs
    obtain rfl := Option.some.inj hs
    have hra : r = lo := by simpa using hr
    obtain ⟨b, hb, htb⟩ := c_pred hl (by omega) (by omega)
    have hbpc : b.pc + 1 = t.pc := pred_pc htb ⟨by omega, by omega⟩ (Or.inr (by omega))
    have hbh := c_halves hp hX hf hS h5 lane hb hn (by omega)
    obtain ⟨ins, hci, -, hk⟩ := win_cases htb
    have e1' : kernel.code[b.pc]? = some ⟨none, .cvt c1⟩ := by
      rw [show b.pc = 1304 + 4 * n by omega]; exact e1
    obtain rfl : ins = ⟨none, .cvt c1⟩ := Option.some.inj (hci.symm.trans e1')
    have hem : Assumptions.emuSites.contains b.pc = false := by
      have := List.all_eq_true.mp emu_c b.pc (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
      simpa using this
    rcases hk with ⟨hg, -, -⟩ | ⟨-, -, hk'⟩
    · simp at hg
    · obtain ⟨v, hv, hh⟩ := hbh.1
      refine ⟨v, ?_, hh⟩
      rw [hra, hk' lo hw1 (fun h => by rw [hem] at h; cases h), hlo]
      exact hv
  · exfalso
    have hsc := scanCode_get mod3_scan hc
    rw [Nat.zero_add] at hsc
    simp [hs] at hsc
    omega

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
