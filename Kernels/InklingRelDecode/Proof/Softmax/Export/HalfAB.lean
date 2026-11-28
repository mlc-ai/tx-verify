-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.LateValues
public import Kernels.InklingRelDecode.Flow.Sites.Part000
import Kernels.InklingRelDecode.Proof.Softmax.Data.HalfWin
import Kernels.InklingRelDecode.Proof.Softmax.Data.WordsTy
import Kernels.InklingRelDecode.Proof.Softmax.Data.LaneStop
import Kernels.InklingRelDecode.Proof.Softmax.Export.BiasHalf

/-! # The registers of the bias packs hold halves

A state of a lane at a pack of the bias words (pcs 816 to 847 for the preloads', 1014 to 1045 for
the loop's) comes from the state after the barrier of pc 575, a preload or the arrival of pc 1013;
the types of the table's registers hold there (the preloads return bf16 numbers, `bias_half`) and
the local steps keep them (`ty_reach`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Assumption PTX.Flow.TyG Control Data Lib

variable {Q : Params} {L : Launch} {g : Nat}

set_option maxRecDepth 100000

private theorem keysA_ld (j : Nat) (hj : j < 64) : ∀ r ∈ wKeys .a (681 + 2 * j),
    r = 199 ∨ ∃ i, i ≤ j ∧ r = 263 + i := by
  intro r hr
  have h1 : ¬ 2560 ≤ 681 + 2 * j := by omega
  have h2 : (681 + 2 * j - 678) / 2 = j + 1 := by omega
  have h3 : 681 + 2 * j < 848 := by omega
  have h4 : ¬ 1123 ≤ 681 + 2 * j := by omega
  have h5 : 681 + 2 * j - 816 = 0 := by omega
  simp [wKeys, h1, h3, h4, h5, preCnt, h2, pkCnt, preReg] at hr
  rcases hr with rfl | ⟨i, hi, rfl⟩
  · exact .inl rfl
  · exact .inr ⟨i, by omega, rfl⟩

private theorem keysA_pk (pc : Nat) (h1 : 816 ≤ pc) (h2 : pc < 848) (r : Nat) (h3 : 263 ≤ r)
    (h4 : r < 327) : r ∈ wKeys .a pc := by
  have e1 : ¬ 2560 ≤ pc := by omega
  have e2 : min 64 ((pc - 678) / 2) = 64 := by omega
  simp [wKeys, e1, h2, preCnt, e2, preReg]
  right; left
  exact ⟨r - 263, by omega, by omega⟩

private theorem keysB_pk (pc : Nat) (h1 : 1014 ≤ pc) (h2 : pc < 1046) (i : Nat) (h3 : i < 64) :
    nxtReg i ∈ wKeys .b pc := by
  have e1 : ¬ 2560 ≤ pc := by omega
  have e2 : ¬ 1123 ≤ pc := by omega
  simp [wKeys, e1, e2, h2, nwK]
  left
  exact ⟨i, h3, rfl⟩

private theorem keys_edge : wKeys .a 575 = [199] ∧ wKeys .a 576 = [199] ∧
    (∀ pc, 1012 ≤ pc → pc ≤ 1014 → wKeys .b pc = nwK) := by
  refine ⟨by decide +kernel, by decide +kernel, fun pc h1 h2 => ?_⟩
  rcases (by omega : pc = 1012 ∨ pc = 1013 ∨ pc = 1014) with rfl | rfl | rfl <;> decide +kernel

private theorem region_edge : ∀ pc, 575 ≤ pc → pc ≤ 576 → (inIvs (wIvs .a) pc || evAtB kernel pc) =
    true := by
  intro pc h1 h2
  rcases (by omega : pc = 575 ∨ pc = 576) with rfl | rfl <;> decide +kernel

private theorem region_arr : ∀ pc, 1012 ≤ pc → pc ≤ 1014 →
    (inIvs (wIvs .b) pc || evAtB kernel pc) = true := by
  intro pc h1 h2
  rcases (by omega : pc = 1012 ∨ pc = 1013 ∨ pc = 1014) with rfl | rfl | rfl <;> decide +kernel

private theorem keep575 : (match kernel.code[575]? with
    | some ins => !(EventFrame.eventWrites ins.op).contains 199 | none => true) = true := by
  decide +kernel

private theorem keepLd : ∀ j : Fin 64, (match kernel.code[680 + 2 * j.val]? with
    | some ins => (199 :: (List.range j.val).map (263 + ·)).all fun r =>
        !(EventFrame.eventWrites ins.op).contains r
    | none => true) = true := by
  decide +kernel

private theorem keepArr : ∀ q ∈ [1012, 1013], (match kernel.code[q]? with
    | some ins => nwK.all fun r => !(EventFrame.eventWrites ins.op).contains r
    | none => true) = true := by
  decide +kernel

private theorem ld64 : ∀ j : Fin 64, ldB (680 + 2 * j.val) (263 + j.val) = true := by
  decide +kernel

private theorem site_575 (s : Site) (h : s.pc = 575) : s = .bar0 := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem site_1013 (s : Site) (h : s.pc = 1012 ∨ s.pc = 1013) :
    s = .bar21 ∨ s = .arrive := by
  revert h
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

private theorem site_pre (s : Site) (h1 : 680 ≤ s.pc) (h2 : s.pc ≤ 806) (h3 : s.pc % 2 = 0) :
    ∃ j : Fin 64, s = .pre j := by
  cases s with
  | pre j => exact ⟨j, rfl⟩
  | nxt j => simp only [Site.pc] at h2; omega
  | _ => exfalso; revert h1 h2 h3; decide +kernel

/-- **The state after a preload has the types of the table**, or is faulted at the preload. -/
private theorem start_ld {m : Mem0} {X : Execution} {t0 sp : TState} {e : Event} {k j : Nat}
    {ent : Entry} {y : Data.D} (hj : j < 64) (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hk : X.get (g, k) = some e) (hep : e.pc = 680 + 2 * j)
    (hat : (codeS ent L g).AtD y sp) (hsite : y.c.site = .pre ⟨j, hj⟩) (typ : VTyp y.v)
    (hes : EStep kernel Assumptions.all L g sp e (some t0)) :
    (t0.fault = none ∧ TyGood .a t0) ∨ (t0.fault ≠ none ∧ t0.pc = 680 + 2 * j) := by
  have hspc : sp.pc = 680 + 2 * j := (EventFrame.estep_source_pc hes).symm.trans hep
  obtain ⟨ins, hci, -, hfi⟩ := EventFrame.estep_event_source hes
  obtain ⟨p, a, hc, hk', hnc, he', hreg⟩ := ldB_spec (ld64 ⟨j, hj⟩)
  rw [hspc] at hci
  obtain rfl : ins = ⟨some (p, false), .mem a⟩ := Option.some.inj (hci.symm.trans hc)
  obtain ⟨x, bs, rfl, ht0⟩ := fires_load hk' hnc hfi he'
  obtain ⟨-, hsub0, hacc0, hflt, -⟩ := id hat
  have hsub : sp.sub = 0 := hsub0.trans rfl
  have hacc : sp.acc = [] := hacc0.trans rfl
  cases hv : rebuild 3 bs with
  | error f =>
    right
    have : t0 = { sp with fault := some f } := by rw [ht0]; simp [afterLoad, hv]
    subst this
    exact ⟨by simp, hspc⟩
  | ok v =>
    left
    obtain ⟨x', hx'⟩ := bias_half hp hX hf hk (.inl ⟨⟨j, hj⟩, hspc⟩)
    rw [hv] at hx'
    have hvv : v = .float .bf16 x' := Except.ok.inj hx'
    have e0 : t0 = { setReg sp (263 + j) v with pc := sp.pc + 1, sub := 0, acc := [] } := by
      rw [ht0, hreg]
      exact afterLoad_ok hsub hacc hv
    have hpc : t0.pc = 681 + 2 * j := by rw [e0]; simp [hspc]; omega
    have h199 : sp.regs 199 = some dflt :=
      holds_mem (atS_const hat).1 (by simp [startF, dflt])
    have hwf : Holds sp.regs (wordF preReg y.v.ld j) := by
      have := atS_wFat hat
      simpa [wF, hsite, wFS] using this
    refine ⟨by rw [e0]; simpa [setReg] using hflt, ?_, ?_⟩
    · have : inIvs (wIvs .a) (681 + 2 * j) = true := by simp [inIvs, wIvs]; omega
      rw [hpc]
      simp [this]
    · intro r hr
      rw [hpc] at hr
      rcases keysA_ld j hj r hr with rfl | ⟨i, hi, rfl⟩
      · refine ⟨dflt, ?_, tyk_half (by omega) (.inl ⟨0, rfl⟩)⟩
        rw [e0]
        simpa [setReg, show (199 : Nat) ≠ 263 + j by omega] using h199
      · rcases Nat.lt_or_ge i j with hij | hij
        · have hm : (preReg i, y.v.ld i) ∈ wordF preReg y.v.ld j :=
            List.mem_map.mpr ⟨i, List.mem_range.mpr hij, rfl⟩
          have := holds_mem hwf hm
          refine ⟨y.v.ld i, ?_, tyk_half (by omega) (bw_half (typ.ld i))⟩
          rw [e0]
          simp only [setReg]
          rw [Function.update_of_ne (by omega)]
          exact this
        · obtain rfl : i = j := by omega
          refine ⟨v, by rw [e0]; simp [setReg], tyk_half (by omega) ?_⟩
          rw [hvv]
          exact .inr ⟨x', rfl⟩

/-- **The state after the barrier of pc 575 has the types of the table.** -/
private theorem start_bar {t0 sp : TState} {e : Event} {ent : Entry} {y : Data.D}
    (hep : e.pc = 575) (hat : (codeS ent L g).AtD y sp)
    (hes : EStep kernel Assumptions.all L g sp e (some t0)) : TyGood .a t0 := by
  have hspc : sp.pc = 575 := (EventFrame.estep_source_pc hes).symm.trans hep
  obtain ⟨ins, hci, -, -⟩ := EventFrame.estep_event_source hes
  have hnw : 199 ∉ EventFrame.eventWrites ins.op := by
    have := keep575
    rw [hspc] at hci
    rw [hci] at this
    simpa using this
  have h199 : sp.regs 199 = some dflt := holds_mem (atS_const hat).1 (by simp [startF, dflt])
  have hp := post_pc hes
  rw [hspc] at hp
  have hk : wKeys .a t0.pc = [199] := by
    rcases (by omega : t0.pc = 575 ∨ t0.pc = 576) with h | h <;> rw [h]
    exacts [keys_edge.1, keys_edge.2.1]
  refine ⟨region_edge _ (by omega) (by omega), fun r hr => ?_⟩
  rw [hk] at hr
  obtain rfl := List.mem_singleton.mp hr
  refine ⟨dflt, ?_, tyk_half (by omega) (.inl ⟨0, rfl⟩)⟩
  rw [estep_keeps hes ins hci 199 hnw]
  exact h199

/-- **The state after the barrier of pc 1012 or the arrival of pc 1013 has the types of the
table.** -/
private theorem start_arr {t0 sp : TState} {e : Event} {ent : Entry} {y : Data.D}
    (hep : e.pc = 1012 ∨ e.pc = 1013) (hat : (codeS ent L g).AtD y sp)
    (hsite : y.c.site = .bar21 ∨ y.c.site = .arrive)
    (typ : VTyp y.v) (hes : EStep kernel Assumptions.all L g sp e (some t0)) : TyGood .b t0 := by
  have hspc : sp.pc = e.pc := (EventFrame.estep_source_pc hes).symm
  obtain ⟨ins, hci, -, -⟩ := EventFrame.estep_event_source hes
  have hnw : ∀ r ∈ nwK, r ∉ EventFrame.eventWrites ins.op := by
    have := keepArr e.pc (by simpa using hep)
    rw [hspc] at hci
    rw [hci] at this
    intro r hr
    simpa using List.all_eq_true.mp this r hr
  have hwf : Holds sp.regs (wordF nxtReg y.v.ld 64) := by
    have := atS_wFat hat
    rcases hsite with h | h <;> simpa [wF, h, wFS, wN, wP] using this
  have hp := post_pc hes
  have hk : wKeys .b t0.pc = nwK := keys_edge.2.2 _ (by omega) (by omega)
  refine ⟨region_arr _ (by omega) (by omega), fun r hr => ?_⟩
  rw [hk] at hr
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
  have hi' := List.mem_range.mp hi
  have := holds_mem hwf (List.mem_map.mpr ⟨i, hi, rfl⟩)
  refine ⟨y.v.ld i, ?_, tyk_half ?_ (bw_half (typ.ld i))⟩
  · rw [estep_keeps hes ins hci _ (hnw _ hr)]
    exact this
  · simp only [nxtReg]
    split_ifs <;> omega

/-- **At a pack of the bias words the table's registers hold typed values.** -/
private theorem ab_typed {m : Mem0} {X : Execution} {t : TState}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hS : ∀ k a vals sh, X.get (g, k) = some ⟨Flow.tmemLoad_0, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x)
    (h5 : g % L.block < 128 → ∀ k mode sent b c recv ok,
      X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩ → SK.ni.Has sent ∧ SK.ni.Has recv)
    (lane : g % L.block < 128) (hl : Iface.LaneState L X g t)
    (hpc : (816 ≤ t.pc ∧ t.pc < 848) ∨ (1014 ≤ t.pc ∧ t.pc < 1046)) :
    ((816 ≤ t.pc ∧ t.pc < 848) → TyAt .a t) ∧ ((1014 ≤ t.pc ∧ t.pc < 1046) → TyAt .b t) := by
  have hin : inS ceWin t.pc = true := by simp only [inS, ceWin]; simp; omega
  obtain ⟨k, e, t0, hk, hr1, ⟨s, hes⟩, hev, hin0, hrt, -⟩ :=
    lane_set ce_fwd ce_enter ce_zero hl hin
  have hpost := post_pc hes
  have hspc := EventFrame.estep_source_pc hes
  have hcls := ce_events e.pc hev
  simp only [inS, ceWin, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true,
    decide_eq_true_eq] at hin0
  have keep_in : ∀ {S : List (Nat × Nat)}, fwdOk S [] = true → inS S t0.pc = true →
      inS S t.pc = true := fun hw h => (win_keep hw hrt h).1
  by_cases hA : 816 ≤ t.pc ∧ t.pc < 848
  · have hcA : e.pc = 575 ∨ (680 ≤ e.pc ∧ e.pc ≤ 806 ∧ e.pc % 2 = 0) := by
      rcases hcls with h | h | h | h | h
      · exact .inl h
      · exact .inr h
      all_goals
        exfalso
        have h1 : inS hiWin t0.pc = true := by simp only [inS, hiWin]; simp; omega
        have := keep_in hi_fwd h1
        simp only [inS, hiWin] at this; simp at this; omega
    refine ⟨fun _ => ?_, fun h => absurd h.1 (by omega)⟩
    obtain ⟨ent, y, sp, hsite, hat, hes', typ, ni⟩ :=
      lane_stop hp hX hf hS h5 lane hk hr1 (by omega) (by omega)
    rcases hcA with h | ⟨h1, h2, h3⟩
    · exact (ty_reach (start_bar h hat hes') hrt).2
    · obtain ⟨j, hj⟩ := site_pre y.c.site (by omega) (by omega) (by omega)
      have hep : e.pc = 680 + 2 * j.val := by rw [← hsite, hj]; rfl
      rcases start_ld j.isLt hp hX hf hk hep hat hj typ hes' with ⟨-, h0⟩ | ⟨hfa, hq⟩
      · exact (ty_reach h0 hrt).2
      · exfalso
        rcases Relation.ReflTransGen.cases_head hrt with rfl | ⟨c, hc, -⟩
        · omega
        · obtain ⟨-, -, hfa', -⟩ := win_cases hc
          exact hfa hfa'
  · have hB : 1014 ≤ t.pc ∧ t.pc < 1046 := hpc.resolve_left hA
    refine ⟨fun h => absurd h hA, fun _ => ?_⟩
    have h13 : e.pc = 1012 ∨ e.pc = 1013 := by
      rcases hcls with h | h | h | h | h
      all_goals try (first | exact .inl h | exact .inr h)
      all_goals exfalso
      · have h1 : inS loWin t0.pc = true := by simp only [inS, loWin]; simp; omega
        have := keep_in lo_fwd h1
        simp only [inS, loWin] at this; simp at this; omega
      · have h1 : inS loWin t0.pc = true := by simp only [inS, loWin]; simp; omega
        have := keep_in lo_fwd h1
        simp only [inS, loWin] at this; simp at this; omega
      · have h1 : inS hi2Win t0.pc = true := by simp only [inS, hi2Win]; simp; omega
        have := keep_in hi2_fwd h1
        simp only [inS, hi2Win] at this; simp at this; omega
    obtain ⟨ent, y, sp, hsite, hat, hes', typ, ni⟩ :=
      lane_stop hp hX hf hS h5 lane hk hr1 (by omega) (by omega)
    have hst := site_1013 y.c.site (by rw [hsite]; exact h13)
    exact (ty_reach (start_arr h13 hat hst typ hes') hrt).2

/-- The source registers of the packs, by range: the preloads' words (`a`) or the loop's. -/
private def srcOk (a : Bool) (op : Op) : Bool :=
  match Iface.halfSrcs op with
  | some srcs => srcs.all (fun o => match o with
      | .reg r => if a then decide (263 ≤ r ∧ r < 327) else decide (r = 332 ∨ (334 ≤ r ∧ r < 397))
      | _ => true) && (match op with | .move m => m.kind == .pack | _ => false)
  | none => false

private theorem src_scan : scanCode (fun pc ins =>
    decide (pc < 816 ∨ (848 ≤ pc ∧ pc < 1014) ∨ 1046 ≤ pc) || srcOk (decide (pc < 848)) ins.op)
    kernel.code 0 = true := by
  decide +kernel

private theorem nxt_of {r : Nat} (h : r = 332 ∨ (334 ≤ r ∧ r < 397)) :
    ∃ i, i < 64 ∧ r = nxtReg i := by
  rcases h with rfl | h
  · exact ⟨0, by omega, rfl⟩
  · exact ⟨r - 333, by omega, by simp only [nxtReg]; split_ifs <;> omega⟩

/-- **The registers a pack of the bias words reads hold halves** (pcs 816 to 847 and 1014 to
1045). -/
public theorem half_ab {m : Mem0} {X : Execution} {t : TState}
    (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hS : ∀ k a vals sh, X.get (g, k) = some ⟨Flow.tmemLoad_0, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x)
    (h5 : g % L.block < 128 → ∀ k mode sent b c recv ok,
      X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩ → SK.ni.Has sent ∧ SK.ni.Has recv)
    (lane : g % L.block < 128) (hl : Iface.LaneState L X g t)
    (hpc : (816 ≤ t.pc ∧ t.pc < 848) ∨ (1014 ≤ t.pc ∧ t.pc < 1046)) {i : Instr}
    (hc : kernel.code[t.pc]? = some i) {srcs : List Opnd} (hs : Iface.halfSrcs i.op = some srcs)
    {r : Nat} (hr : .reg r ∈ srcs) : ∃ v, t.regs r = some v ∧ TyG.halfSrcOk i.op v := by
  have hsc := scanCode_get src_scan hc
  rw [Nat.zero_add] at hsc
  obtain ⟨hA, hB⟩ := ab_typed hp hX hf hS h5 lane hl hpc
  have hs' : srcOk (decide (t.pc < 848)) i.op = true := by
    simpa [show ¬(t.pc < 816 ∨ (848 ≤ t.pc ∧ t.pc < 1014) ∨ 1046 ≤ t.pc) by omega] using hsc
  simp only [srcOk, hs, Bool.and_eq_true, List.all_eq_true] at hs'
  obtain ⟨hall, hpk⟩ := hs'
  have hop : ∀ v, TyG.halfSrcOk i.op v = Half16 v := by
    intro v
    cases hop : i.op with
    | move mv =>
      cases mv with
      | mk kind ty dsts ms =>
        simp only [hop, beq_iff_eq] at hpk
        subst hpk
        rfl
    | _ => simp [hop] at hpk
  have hr' := hall _ hr
  by_cases ha : t.pc < 848
  · have hA' := hA ⟨by omega, ha⟩
    simp only [ha, decide_true, ↓reduceIte, decide_eq_true_eq] at hr'
    obtain ⟨v, hv, hk⟩ := hA' r (keysA_pk _ (by omega) ha r hr'.1 hr'.2)
    refine ⟨v, hv, ?_⟩
    rw [hop]
    simpa [TyK, show ¬(1916 ≤ r ∧ r < 1948) by omega] using hk
  · have hB' := hB ⟨by omega, by omega⟩
    simp only [ha, decide_false, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hr'
    obtain ⟨n, hn, rfl⟩ := nxt_of hr'
    obtain ⟨v, hv, hk⟩ := hB' _ (keysB_pk _ (by omega) (by omega) n hn)
    refine ⟨v, hv, ?_⟩
    rw [hop]
    have : ¬(1916 ≤ nxtReg n ∧ nxtReg n < 1948) := by simp only [nxtReg]; split_ifs <;> omega
    simpa [TyK, this] using hk

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
