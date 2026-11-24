-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.NcInputFootprint
public import Lemmas.Flow.TraceInduction
public import Lemmas.Flow.Final

@[expose] public section

/-! # Tracking the index producer along its firing events -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1Index

open PTX PTX.Flow PTX.Proof

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0}

private def lengthBindings (P : Params) (s : Site) : Prop :=
  (s = .lenOrig → ∃ x, P.topkLenBase = some x) ∧
    (s = .lenExtra → ∃ x, P.extraTopkLenBase = some x)

private theorem lengthBindings_init {g : Nat} : lengthBindings P (init P L g).site := by
  cases h0 : P.topkLenBase <;> cases h1 : P.extraTopkLenBase <;>
    simp [lengthBindings, init, firstSite, h0, h1]

private theorem lengthBindings_next {g : Nat} {d d' : D} {e : Event}
    (hb : lengthBindings P d.site) (hn : next P L g d e = some (some d')) :
    lengthBindings P d'.site := by
  cases hs : d.site <;> simp only [next, nextSite, hs] at hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals
    simp only [afterPairFirst, afterReady, lengthBindings] at *
    repeat' split_ifs
    all_goals cases hP : P.extraTopkLenBase <;> simp_all

private def hasBindings (P : Params) : Option Machine.ThreadD → Prop
  | some (.index d) => lengthBindings P d.site
  | _ => True

private theorem hasBindings_next {g : Nat} {d d' : Option Machine.ThreadD} {e : Event}
    (hb : hasBindings P d) (hn : (Machine.machine P L g).next d e = some d') :
    hasBindings P d' := by
  cases d
  case none =>
    change some none = some d' at hn
    cases hn
    trivial
  case some d =>
    change Machine.next P L g d e = some d' at hn
    cases d
    case prologue s =>
      simp only [Machine.next] at hn
      split at hn
      · cases hn
        trivial
      · split at hn
        · rename_i w _
          split_ifs at hn
          · fin_cases w <;> cases hn <;> trivial
          · cases hn
            trivial
        · cases hn
          trivial
      · cases hn
    case index d =>
      simp only [Machine.next] at hn
      split at hn
      · rename_i d' h
        cases hn
        exact lengthBindings_next (show lengthBindings P d.site from hb) h
      · split_ifs at hn <;> cases hn <;> trivial
      · cases hn
    case head =>
      cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
      simp only [Machine.headStart] at hn
      split_ifs at hn <;> cases hn <;> first | exact lengthBindings_init | trivial
    all_goals
      simp only [Machine.next] at hn
      all_goals repeat' split at hn
      all_goals cases hn
      all_goals trivial

private theorem lengthBindings_of_trace {X : Execution} {g i : Nat} {d : D}
    (hX : Consistent L kernel asms mem0 X) (hs : (Machine.machine P L g).Sound)
    (he : X.get (g, i) ≠ none)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.index d))) :
    lengthBindings P d.site := by
  obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp he
  have hg := Frame.lt_of_get hX he
  exact (hs.produces (hX.thr g hg)).prefix_induction (fun q _ => hasBindings P q) trivial
    (fun _ _ _ _ _ hb _ hn => hasBindings_next hb hn) i (some (.index d)) hd

private theorem fired_site {g : Nat} {d : D} {e : Event} {o : Option TState} {ins : Instr}
    (hf : (Machine.machine P L g).Fired (some (.index d)) e o)
    (hc : kernel.code[d.site.pc]? = some ins) :
    ∃ t, AtD P L g d t ∧ Inv P L g d ∧ Fires d.site.pc (eventTmpl asms L g t ins.op) e o := by
  obtain ⟨t, ⟨hat, hi⟩, hf⟩ := hf
  change AtD P L g d t at hat
  change Inv P L g d at hi
  change Fires t.pc (match kernel.code[d.site.pc]? with
    | some ins => eventTmpl asms L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  rw [hc, hat.1] at hf
  exact ⟨t, hat, hi, hf⟩

private theorem length_event {g pc base dst addr : Nat} {t u : TState} {e : Event}
    (hpc : t.pc = pc) (hs : t.sub = 0) (hr : t.regs base = some (b64 addr))
    (ha : addr < 2 ^ 64) (hal : addr % 4 = 0) (hnc : ncLoads.contains pc = true)
    (hf : Fires pc (eventTmpl asms L g t (.mem
      {kind := .load, space := some .global, sem := .weak, elem := .int .s 32, nc := true,
       addr := ⟨.reg base 64, 0⟩, dsts := [some dst]})) e (some u)) :
    ∃ bs, LaunchReads.ReadsLaunchWord e addr bs := by
  have hnc' : asms.any (·.ncLoads t.pc) = true := by
    rw [hpc]
    exact List.any_eq_true.mpr ⟨Assumptions.ncReadOnly, by simp [Assumptions.all], hnc⟩
  rw [eventTmpl, memTmpl_direct_weakLoad (sp := .global) (base := base) (w := 64)
    rfl rfl rfl rfl rfl] at hf
  change Fires pc (loadTmpl asms L g t .global true 32 [dst] base 0) e (some u) at hf
  rw [loadTmpl_global_nc hs hr ha (by decide) hal hnc'] at hf
  obtain ⟨bs, _, he, _⟩ := hf
  exact ⟨bs, congrArg Event.kind he, by rw [he]; exact hnc⟩

private theorem main_length {g ptr : Nat} {d : D} {e : Event} {u : TState}
    (hpre : Pre P L mem0) (hb : eOf L g < P.b) (hp : P.topkLenBase = some ptr)
    (hs : d.site = .lenOrig) (hf : (Machine.machine P L g).Fired (some (.index d)) e (some u)) :
    ∃ bs, LaunchReads.ReadsLaunchWord e (ptr + 4 * eOf L g) bs := by
  have hc : kernel.code[d.site.pc]? = some ⟨none, .mem ncLenOrig⟩ := by
    rw [hs]
    exact Flow.code_2360
  obtain ⟨t, hat, _, hf⟩ := fired_site hf hc
  have hsub : t.sub = 0 := by rw [hat.2.1, hs]; rfl
  have hpc : t.pc = 2360 := by rw [hat.1, hs]; rfl
  have hr := hat.reg (r := 3023) (by rw [hs]; decide +kernel)
  change t.regs 3023 = some (b64 ((Thread.paramWord L 80 8 + 4 * eOf L g) % 2 ^ 64)) at hr
  have hal := Thread.paramAddr_mod4 (Thread.paramWord_80_mod4 hpre) g
  change (Thread.paramWord L 80 8 + 4 * eOf L g) % 2 ^ 64 % 4 = 0 at hal
  have hp64 := hpre.topkLenBaseLt ptr hp
  have hspan := (hpre.topkLenAddressable ptr hp).2.2
  have ha : ptr + 4 * eOf L g < 2 ^ 64 := by omega
  rw [show Thread.paramWord L 80 8 = ptr % 2 ^ 64 from Thread.paramWord_80_some hpre hp,
    Nat.mod_eq_of_lt hp64, Nat.mod_eq_of_lt ha] at hr hal
  rw [hs] at hf
  exact length_event hpc hsub hr ha hal (by decide) hf

private theorem extra_length {g ptr : Nat} {d : D} {e : Event} {u : TState}
    (hpre : Pre P L mem0) (hb : eOf L g < P.b) (hp : P.extraTopkLenBase = some ptr)
    (hs : d.site = .lenExtra) (hf : (Machine.machine P L g).Fired (some (.index d)) e (some u)) :
    ∃ bs, LaunchReads.ReadsLaunchWord e (ptr + 4 * eOf L g) bs := by
  have hc : kernel.code[d.site.pc]? = some ⟨none, .mem ncLenExtra⟩ := by
    rw [hs]
    exact Flow.code_2365
  obtain ⟨t, hat, _, hf⟩ := fired_site hf hc
  have hsub : t.sub = 0 := by rw [hat.2.1, hs]; rfl
  have hpc : t.pc = 2365 := by rw [hat.1, hs]; rfl
  have hr := hat.reg (r := 3025) (by rw [hs]; decide +kernel)
  change t.regs 3025 = some (b64 ((Thread.paramWord L 144 8 + 4 * eOf L g) % 2 ^ 64)) at hr
  have hal := Thread.paramAddr_mod4 (Thread.paramWord_144_mod4 hpre) g
  change (Thread.paramWord L 144 8 + 4 * eOf L g) % 2 ^ 64 % 4 = 0 at hal
  have hp64 := hpre.extraTopkLenBaseLt ptr hp
  have hspan := (hpre.extraTopkLenAddressable ptr hp).2.2
  have ha : ptr + 4 * eOf L g < 2 ^ 64 := by omega
  rw [show Thread.paramWord L 144 8 = ptr % 2 ^ 64 from Thread.paramWord_144_some hpre hp,
    Nat.mod_eq_of_lt hp64, Nat.mod_eq_of_lt ha] at hr hal
  rw [hs] at hf
  exact length_event hpc hsub hr ha hal (by decide) hf

private theorem signedWord_of_lt {n : Nat} (hn : n < 2 ^ 31) :
    toSigned 32 (truncBits 32 (BitVec.ofNat 64 n)) = (n : Int) := by
  rw [truncBits_ofNat (by omega : n < 2 ^ 32) (by decide), toSigned_eq_toInt32]
  simp only [CeilDiv.toInt32, FastDivmod.W]
  omega

private theorem signedCast_of_lt {n : Nat} (hn : n < 2 ^ 31) : cvtS32 n = n := by
  unfold cvtS32
  rw [signedWord_of_lt hn]
  omega

private theorem signedProduct_of_lt {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (hab : a * b < 2 ^ 64) : mulWideS32 a b = a * b := by
  unfold mulWideS32
  rw [signedWord_of_lt ha, signedWord_of_lt hb, ← Nat.cast_mul (α := Int)]
  omega

private theorem rowWord_lt {batch query e q stride j : Nat}
    (he : e < batch) (hq : q < query) (hj : j < stride) :
    (e * query + q) * stride + j < batch * query * stride := by
  have hr : e * query + q + 1 ≤ batch * query := by
    calc
      _ ≤ (e + 1) * query := by rw [Nat.add_mul, Nat.one_mul]; omega
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  calc
    _ < (e * query + q + 1) * stride := by simp only [Nat.add_mul, Nat.one_mul]; omega
    _ ≤ _ := Nat.mul_le_mul_right _ hr

set_option maxHeartbeats 1000000 in
private theorem main_pair_addr {g b : Nat} (hpre : Pre P L mem0)
    (hb : eOf L g < P.b) (hq : qOf L g < P.s_q)
    (hpos : 64 * b + 2 * laneOf L g < P.topk) :
    pairAddr P L g b =
      P.indicesBase + 4 * ((eOf L g * P.s_q + qOf L g) * P.topk + 64 * b + 2 * laneOf L g) := by
  have hword := rowWord_lt hb hq hpos
  have hspan := hpre.indicesAddressable
  have htotal : P.indicesBase +
      4 * ((eOf L g * P.s_q + qOf L g) * P.topk + (64 * b + 2 * laneOf L g)) < 2 ^ 64 := by
    rw [show 4 * P.b * P.s_q * P.topk = 4 * (P.b * P.s_q * P.topk) by ring] at hspan
    omega
  have hrow : P.indicesBase + 4 * ((eOf L g * P.s_q + qOf L g) * P.topk) < 2 ^ 64 := by
    omega
  have hq31 : P.topk * qOf L g < 2 ^ 31 := by
    rw [Nat.mul_comm P.topk]
    exact (Nat.mul_lt_mul_of_pos_right hq hpre.topkPos).trans hpre.topkRange
  have hb31 := hpre.mainIndexBatchOffsetLt hb
  have htk31 := (Nat.le_mul_of_pos_left P.topk hpre.sqPos).trans_lt hpre.topkRange
  have htl : 2 * laneOf L g < 64 := by
    have h := Nat.mod_lt (tidOf L g) (by decide : 0 < 32)
    change tidOf L g % 32 < 32 at h
    change 2 * (tidOf L g % 32) < 64
    omega
  have hoff : idxRowOff P L g = (eOf L g * P.s_q + qOf L g) * P.topk := by
    unfold idxRowOff
    rw [Thread.paramWord_four hpre.paramStrideIndicesSq,
      Thread.paramWord_four hpre.paramStrideIndicesB]
    have ht32 : P.topk < 2 ^ 32 := by omega
    have htk32 : P.s_q * P.topk < 2 ^ 32 := hpre.topkRange.trans (by decide)
    have hq32 : P.topk * qOf L g < 4294967296 := by omega
    have hb31' : P.s_q * P.topk * eOf L g < 2 ^ 31 := by rw [Nat.mul_comm]; exact hb31
    have hb32 : P.s_q * P.topk * eOf L g < 4294967296 := by omega
    rw [show ctaidX L g = qOf L g from rfl, show ctaidY L g = eOf L g from rfl]
    simp only [Nat.mod_eq_of_lt ht32, Nat.mod_eq_of_lt htk32,
      Nat.mod_eq_of_lt hq32, Nat.mod_eq_of_lt hb32, signedCast_of_lt hq31,
      signedCast_of_lt hb31']
    have hm : P.topk * qOf L g + P.s_q * P.topk * eOf L g =
        (eOf L g * P.s_q + qOf L g) * P.topk := by ring
    rw [hm]
    exact Nat.mod_eq_of_lt (by omega : _ < 18446744073709551616)
  unfold pairAddr
  rw [Thread.paramWord_eight hpre.paramIndices, hoff]
  have hbase : P.indicesBase < 2 ^ 64 := by omega
  have hm : (eOf L g * P.s_q + qOf L g) * P.topk < 2 ^ 64 := by omega
  have hm4 : (eOf L g * P.s_q + qOf L g) * P.topk * 4 < 2 ^ 64 := by omega
  have hsum : P.indicesBase + (eOf L g * P.s_q + qOf L g) * P.topk * 4 < 2 ^ 64 := by omega
  rw [Nat.mod_mod, Nat.mod_eq_of_lt hbase, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hm4,
    Nat.mod_eq_of_lt hsum, Nat.mod_eq_of_lt (by omega : 2 * laneOf L g < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : 2 * laneOf L g * 4 < 2 ^ 64)]
  omega

set_option maxHeartbeats 1000000 in
private theorem extra_pair_addr {g b : Nat} (hpre : Pre P L mem0)
    (hb : eOf L g < P.b) (hq : qOf L g < P.s_q)
    (hpos : 64 * b + 2 * laneOf L g < P.extra_topk) :
    extraPairAddr P L g b =
      P.extraIndicesBase + 4 *
        ((eOf L g * P.s_q + qOf L g) * P.extra_topk + 64 * b + 2 * laneOf L g) := by
  have hp : 0 < P.extra_topk := by omega
  have hword := rowWord_lt hb hq hpos
  have hspan := hpre.extraIndicesAddressable hp
  have htotal : P.extraIndicesBase +
      4 * ((eOf L g * P.s_q + qOf L g) * P.extra_topk + (64 * b + 2 * laneOf L g)) < 2 ^ 64 := by
    rw [show 4 * P.b * P.s_q * P.extra_topk = 4 * (P.b * P.s_q * P.extra_topk) by ring] at hspan
    omega
  have hrow : P.extraIndicesBase + 4 * ((eOf L g * P.s_q + qOf L g) * P.extra_topk) < 2 ^ 64 := by
    omega
  have hq31 : P.extra_topk * qOf L g < 2 ^ 31 := by
    rw [Nat.mul_comm P.extra_topk]
    exact (Nat.mul_lt_mul_of_pos_right hq hp).trans hpre.extraTopkRange
  have hb31 : eOf L g < 2 ^ 31 := hb.trans hpre.bLt
  have hb63 := hpre.extraIndexBatchOffsetLt hb
  have htk31 := (Nat.le_mul_of_pos_left P.extra_topk hpre.sqPos).trans_lt hpre.extraTopkRange
  have htl : 2 * laneOf L g < 64 := by
    have h := Nat.mod_lt (tidOf L g) (by decide : 0 < 32)
    change tidOf L g % 32 < 32 at h
    change 2 * (tidOf L g % 32) < 64
    omega
  have hm : (eOf L g * P.s_q + qOf L g) * P.extra_topk < 2 ^ 64 := by omega
  have hm4 : (eOf L g * P.s_q + qOf L g) * P.extra_topk * 4 < 2 ^ 64 := by omega
  have hoff : extraRowOff P L g = P.extraIndicesBase +
      (eOf L g * P.s_q + qOf L g) * P.extra_topk * 4 := by
    unfold extraRowOff
    rw [Thread.paramWord_four hpre.paramStrideExtraIndicesSq,
      Thread.paramWord_four hpre.paramStrideExtraIndicesB,
      Thread.paramWord_eight hpre.paramExtraIndices]
    change
      (P.extraIndicesBase % 2 ^ 64 % 2 ^ 64 +
        ((cvtS32 (P.extra_topk % 2 ^ 32 * qOf L g % 2 ^ 32) % 2 ^ 64 +
         mulWideS32 ((P.s_q * P.extra_topk) % 2 ^ 32) (eOf L g) % 2 ^ 64) %
          (2 ^ 64) % (2 ^ 64) * (4 % (2 ^ 64) % (2 ^ 64)) % (2 ^ 64))) % (2 ^ 64) = _
    rw [Nat.mod_mod, Nat.mod_eq_of_lt (show P.extraIndicesBase < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show P.extra_topk < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show P.s_q * P.extra_topk < 2 ^ 32 from
        hpre.extraTopkRange.trans (by decide)),
      Nat.mod_eq_of_lt (show P.extra_topk * qOf L g < 2 ^ 32 by omega),
      signedCast_of_lt hq31, signedProduct_of_lt hpre.extraTopkRange hb31 (by
        rw [Nat.mul_comm]; exact hb63.trans (by decide)),
      Nat.mod_eq_of_lt (show P.extra_topk * qOf L g < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show P.s_q * P.extra_topk * eOf L g < 2 ^ 64 by
        rw [Nat.mul_comm]; exact hb63.trans (by decide))]
    have hsum : P.extra_topk * qOf L g + P.s_q * P.extra_topk * eOf L g =
        (eOf L g * P.s_q + qOf L g) * P.extra_topk := by ring
    rw [hsum, Nat.mod_mod, Nat.mod_eq_of_lt hm,
      show (4 : Nat) % (2 ^ 64) % (2 ^ 64) = 4 by decide, Nat.mod_eq_of_lt hm4,
      Nat.mod_eq_of_lt (by omega : _ < 2 ^ 64)]
  unfold extraPairAddr
  rw [hoff, Nat.mod_eq_of_lt (by omega : _ < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 2 * laneOf L g < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : 2 * laneOf L g * 4 < 2 ^ 64)]
  omega

private theorem pair_block_bounds {g : Nat} {d : D} {extra first hi : Bool}
    (hs : d.site = .pair extra first hi) (hinv : Inv P L g d) :
    let b := if first then d.block else d.block + 1
    b < totalBlocks d.len0 d.len1 ∧
      isExtraBlock b d.len0 = extra ∧
      (first = true → d.block = if extra then numOrigBlocks d.len0 else 0) := by
  have hp := hinv.pairLoad
  rw [pairInvariant, hs] at hp
  have hm := hinv.tagMain
  have he := hinv.tagExtra
  rw [hs, Site.extra] at hm he
  cases extra <;> cases first
  · simp only [Bool.false_eq_true, ↓reduceIte] at hp ⊢
    exact ⟨hp.1.trans_le (numOrigBlocks_le_totalBlocks _ _),
      by simp [isExtraBlock, not_le.mpr hp.1], by simp⟩
  · have hz := hinv.firstBlock (show d.site = .pair false true false ∨
        d.site = .pair false true true from by cases hi <;> simp [hs])
    simp only [↓reduceIte]
    exact ⟨hinv.block, by simp [isExtraBlock, not_le.mpr (hm rfl)], fun _ => hz⟩
  · simp only [Bool.false_eq_true, ↓reduceIte] at hp ⊢
    exact ⟨hp.1, isExtraBlock_eq_true_iff.mpr (by have := he rfl; omega), by simp⟩
  · simp only [↓reduceIte] at hp ⊢
    exact ⟨hinv.block, isExtraBlock_eq_true_iff.mpr (he rfl), fun _ => hp.1⟩

private def ReadsIndexWord (e : Event) (addr elem : Nat) (bs : List (Option Byte)) : Prop :=
  e.kind = .nc {loc := ⟨.global, 0, addr⟩, size := 4, elem := elem} bs ∧
    ncLoads.contains e.pc = true

private theorem rebuild_index_word {X : Execution} {i : EvId} {e : Event} {addr elem n : Nat}
    {bs : List (Option Byte)} (hX : Consistent L kernel asms mem0 X)
    (hget : X.get i = some e) (hr : ReadsIndexWord e addr elem bs)
    (hmem : ∀ k < 4, mem0 ⟨.global, 0, addr + k⟩ = some (some (word32Byte n k))) :
    rebuild 3 bs = .ok (b32 n) := by
  have hc := hX.asm Assumptions.ncReadOnly (by simp [Assumptions.all])
  rcases e with ⟨pc, kind⟩
  obtain ⟨he, hsite⟩ := hr
  change kind = _ at he
  subst kind
  obtain ⟨hlen, hbytes⟩ := hc i pc _ bs hget hsite
  have heq : bs = (b32 n).toBytes.map some := by
    apply List.ext_getElem?
    intro k
    by_cases hk : k < 4
    · have hv := hbytes k hk _ (hmem k hk)
      simp only [Execution.initialByte, Option.getD_some, Loc.at] at hv
      rw [hv]
      simp [Value.toBytes, b32, word32Byte, List.getElem?_range hk, Value.bytes]
    · have hb : bs.length = 4 := hlen
      rw [List.getElem?_eq_none (by omega)]
      symm
      apply List.getElem?_eq_none
      simpa [Value.toBytes, b32, Value.bytes] using Nat.le_of_not_gt hk
  rw [heq]
  exact rebuild_scalar (show 0 < 4 by decide) rfl

private theorem pair_event {g : Nat} {d : D} {extra first hi : Bool} {e : Event} {u : TState}
    (hs : d.site = .pair extra first hi)
    (hf : (Machine.machine P L g).Fired (some (.index d)) e (some u)) :
    ∃ t bs,
      AtD P L g d t ∧ Inv P L g d ∧
      ∀ a, t.regs (pairOperands extra first).1 = some (b64 a) →
        a < 2 ^ 64 → a % 8 = 0 →
          ReadsIndexWord e (a + 4 * (if hi then 1 else 0)) (if hi then 1 else 0) bs := by
  let op := pairOperands extra first
  let access := ncPair op.1 op.2.1 op.2.2
  have hc : kernel.code[d.site.pc]? = some ⟨none, .mem access⟩ := by
    rw [hs]
    cases extra <;> cases first
    · exact Flow.code_2429
    · exact Flow.code_2403
    · exact Flow.code_2517
    · exact Flow.code_2501
  obtain ⟨t, hat, hinv, hf⟩ := fired_site hf hc
  have hnc : ncLoads.contains d.site.pc = true := by
    rw [hs]
    cases extra <;> cases first <;> cases hi <;> decide
  have hnc' : asms.any (·.ncLoads t.pc) = true := by
    rw [hat.1]
    exact List.any_eq_true.mpr ⟨Assumptions.ncReadOnly, by simp [Assumptions.all], hnc⟩
  have hsub : t.sub = if hi then 1 else 0 := by rw [hat.2.1, hs]; cases hi <;> rfl
  rw [eventTmpl, memTmpl_direct_weakLoad (sp := .global) (base := op.1) (w := 64)
    rfl rfl rfl rfl rfl] at hf
  change Fires d.site.pc (loadTmpl asms L g t .global true 32 [op.2.1, op.2.2] op.1 0) e
    (some u) at hf
  obtain ⟨loc, bs, he, _⟩ := fires_nc_load (a := access) rfl rfl rfl rfl rfl rfl hnc'
    (by
      rw [eventTmpl, memTmpl_direct_weakLoad (sp := .global) (base := op.1) (w := 64)
        rfl rfl rfl rfl rfl, hat.1]
      exact hf)
  refine ⟨t, bs, hat, hinv, fun a hr ha hal => ?_⟩
  change t.regs op.1 = some (b64 a) at hr
  simp only [loadTmpl, effAddr_global hr ha, bind, Except.bind, List.length_cons,
    List.length_nil, Nat.reduceAdd] at hf
  rw [elemAcc_ok (by decide) hal] at hf
  simp only [hnc', true_and, ↓reduceIte] at hf
  obtain ⟨bs', _, he', _⟩ := hf
  have hEq := (congrArg Event.kind he).symm.trans (congrArg Event.kind he')
  have hB := (Kind.nc.inj hEq).2
  exact ⟨by simpa [Loc.at, hsub, ← hB] using congrArg Event.kind he',
    by rw [he']; exact hnc⟩

private theorem pair_geometry {g : Nat} {d : D} {t : TState} {extra first hi : Bool}
    (hpre : Pre P L mem0) (hg : g < L.threads) (hs : d.site = .pair extra first hi)
    (hat : AtD P L g d t) (hinv : Inv P L g d) :
    let b := if first then d.block else d.block + 1
    let j := if hi then 1 else 0
    let l := laneOf L g
    let k := if extra then b - numOrigBlocks d.len0 else b
    let stride := if extra then P.extra_topk else P.topk
    let base := if extra then P.extraIndicesBase else P.indicesBase
    let a := base + 4 * ((eOf L g * P.s_q + qOf L g) * stride + 64 * k + 2 * l)
    t.regs (pairOperands extra first).1 = some (b64 a) ∧ a < 2 ^ 64 ∧ a % 8 = 0 ∧
      64 * k + 2 * l + j < stride ∧ isExtraBlock b d.len0 = extra := by
  dsimp only
  let b := if first then d.block else d.block + 1
  let j := if hi then 1 else 0
  let l := laneOf L g
  have hb : eOf L g < P.b := Wg1Mma.eOf_lt_b hpre
  have hq : qOf L g < P.s_q := Wg1Mma.queryOf_lt hpre hg
  have hl : l < 32 := Nat.mod_lt _ (by decide)
  have hj : j < 2 := by cases hi <;> decide
  obtain ⟨hblock, htag, hfirst⟩ := pair_block_bounds hs hinv
  change b < totalBlocks d.len0 d.len1 at hblock
  change isExtraBlock b d.len0 = extra at htag
  obtain ⟨h0, h1⟩ := And.intro hinv.len0 hinv.len1
  have hreg := hat.reg (r := (pairOperands extra first).1) (by
    rw [hs]
    cases extra <;> cases first <;> cases hi <;> decide +kernel)
  cases extra
  · have hj' : 64 * b + 2 * l + j < P.topk := by
      have hn := (slotPos_lt_origPadded htag hl hj).trans_le
        (Wg1Tma.origPadded_le (by rw [h0]; exact topkLen_le hpre hb) hpre.topkDiv64 hpre.topkPos)
      simpa [slotPos, htag, topkBlock, Nat.mul_comm] using hn
    let a := P.indicesBase + 4 * ((eOf L g * P.s_q + qOf L g) * P.topk + 64 * b + 2 * l)
    have ha : a < 2 ^ 64 := by
      have hr := rowWord_lt hb hq (show 64 * b + 2 * l < P.topk by omega)
      have hspan := hpre.indicesAddressable
      rw [show 4 * P.b * P.s_q * P.topk = 4 * (P.b * P.s_q * P.topk) by ring] at hspan
      dsimp only [a]
      omega
    have hal : a % 8 = 0 := by
      have hbase := hpre.indicesBase
      have hbudget := hpre.topkDiv64
      obtain ⟨n, hn⟩ := Nat.dvd_of_mod_eq_zero hbudget
      simp only [a, hn]
      have heven : (eOf L g * P.s_q + qOf L g) * (64 * n) =
          64 * ((eOf L g * P.s_q + qOf L g) * n) := by ring
      rw [heven]
      omega
    have haddr := main_pair_addr hpre hb hq (show 64 * b + 2 * l < P.topk by omega)
    have hbits : t.regs (pairOperands false first).1 = some (b64 a) := by
      cases first
      · change t.regs 4029 = some (b64 (pairAddr P L g (d.block + 1))) at hreg
        rw [show d.block + 1 = b from rfl, haddr] at hreg
        exact hreg
      · change t.regs 3033 = some (b64 (pairAddr P L g 0)) at hreg
        have hzero : b = 0 := hfirst rfl
        rw [← hzero, haddr] at hreg
        exact hreg
    exact ⟨hbits, ha, hal, hj', htag⟩
  · have hr := slotPos_lt_extraPadded htag hblock hl hj
    let k := b - numOrigBlocks d.len0
    have hj' : 64 * k + 2 * l + j < P.extra_topk := by
      have hlen : d.len1 ≤ P.extra_topk := by rw [h1]; exact extraLen_le hpre hb
      simpa [slotPos, htag, k, topkBlock, Nat.mul_comm] using
        hr.trans_le (Wg1Tma.ceilToMultiple_le hlen hpre.extraDiv64)
    let a := P.extraIndicesBase +
      4 * ((eOf L g * P.s_q + qOf L g) * P.extra_topk + 64 * k + 2 * l)
    have hp : 0 < P.extra_topk := by omega
    have ha : a < 2 ^ 64 := by
      have hr := rowWord_lt hb hq (show 64 * k + 2 * l < P.extra_topk by omega)
      have hspan := hpre.extraIndicesAddressable hp
      rw [show 4 * P.b * P.s_q * P.extra_topk = 4 * (P.b * P.s_q * P.extra_topk) by ring] at hspan
      dsimp only [a]
      omega
    have hmem := hpre.extraIdxInput.resolve_left (by omega)
    have hal : a % 8 = 0 := by
      have hbase := hmem.1
      obtain ⟨n, hn⟩ := Nat.dvd_of_mod_eq_zero hpre.extraDiv64
      simp only [a, hn]
      have heven : (eOf L g * P.s_q + qOf L g) * (64 * n) =
          64 * ((eOf L g * P.s_q + qOf L g) * n) := by ring
      rw [heven]
      omega
    have haddr := extra_pair_addr hpre hb hq (show 64 * k + 2 * l < P.extra_topk by omega)
    have hbits : t.regs (pairOperands true first).1 = some (b64 a) := by
      cases first
      · change t.regs 3043 = some (b64 (extraPairAddr P L g
          (d.block + 1 - numOrigBlocks d.len0))) at hreg
        rw [show d.block + 1 - numOrigBlocks d.len0 = k from rfl, haddr] at hreg
        exact hreg
      · change t.regs 3041 = some (b64 (extraPairAddr P L g 0)) at hreg
        have hz := hfirst rfl
        have hzero : k = 0 := by
          change d.block - numOrigBlocks d.len0 = 0
          simp [hz]
        rw [← hzero, haddr] at hreg
        exact hreg
    exact ⟨hbits, ha, hal, hj', htag⟩

/-- The held index-vector base is an eight-byte aligned, 64-bit global address. -/
theorem pair_operand_bounds {g : Nat} {d : D} {t : TState} {extra first hi : Bool}
    (hpre : Pre P L mem0) (hg : g < L.threads) (hs : d.site = .pair extra first hi)
    (hat : AtD P L g d t) (hinv : Inv P L g d) :
    ∃ a, t.regs (pairOperands extra first).1 = some (b64 a) ∧ a < 2 ^ 64 ∧ a % 8 = 0 := by
  obtain ⟨hbits, ha, hal, _, _⟩ := pair_geometry hpre hg hs hat hinv
  exact ⟨_, hbits, ha, hal⟩

private theorem pair_rebuild {X : Execution} {g i : Nat} {d : D} {e : Event}
    {u : TState} {extra first hi : Bool}
    (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (he : X.get (g, i) = some e) (hs : d.site = .pair extra first hi)
    (hf : (Machine.machine P L g).Fired (some (.index d)) e (some u)) :
    ∃ a bs, e.kind = .nc a bs ∧ NcInputFootprint P a ∧
      rebuild 3 bs = .ok (b32 (ipat (slotIdx P L g
        (if first then d.block else d.block + 1) (laneOf L g) (if hi then 1 else 0)))) := by
  let b := if first then d.block else d.block + 1
  let j := if hi then 1 else 0
  let l := laneOf L g
  have hb : eOf L g < P.b := Wg1Mma.eOf_lt_b hpre
  have hq : qOf L g < P.s_q := Wg1Mma.queryOf_lt hpre (Frame.lt_of_get hX he)
  obtain ⟨t, bs, hat, hinv, hword⟩ := pair_event hs hf
  have h0 := hinv.len0
  obtain ⟨hbits, ha, hal, hj', htag⟩ := pair_geometry hpre (Frame.lt_of_get hX he) hs hat hinv
  cases extra
  · let a := P.indicesBase + 4 * ((eOf L g * P.s_q + qOf L g) * P.topk + 64 * b + 2 * l)
    change a < 2 ^ 64 at ha
    change a % 8 = 0 at hal
    change 64 * b + 2 * l + j < P.topk at hj'
    change isExtraBlock b d.len0 = false at htag
    have hobs := hword a hbits ha hal
    refine ⟨_, bs, hobs.1, .mainIndices ⟨rfl, by dsimp [a]; omega, ?_⟩, ?_⟩
    · have hWord := rowWord_lt hb hq hj'
      dsimp [a]
      rw [show 4 * P.b * P.s_q * P.topk = 4 * (P.b * P.s_q * P.topk) by ring]
      omega
    have htag' : isExtraBlock b (P.topkLen (eOf L g)) = false := h0 ▸ htag
    change rebuild 3 bs = .ok (b32 (ipat (slotIdx P L g b l j)))
    have hidx : slotIdx P L g b l j = P.idx (eOf L g) (qOf L g) (64 * b + 2 * l + j) := by
      simp [slotIdx, slotIndex, slotPos, htag', topkBlock, Nat.mul_comm]
    rw [hidx]
    exact rebuild_index_word hX he hobs fun k hk => by
      have hm := hpre.idxInput _ hb _ hq _ hj' k hk
      simpa [a, j, l, ipat, Nat.mul_add, Nat.add_assoc] using hm
  · let k := b - numOrigBlocks d.len0
    let a := P.extraIndicesBase +
      4 * ((eOf L g * P.s_q + qOf L g) * P.extra_topk + 64 * k + 2 * l)
    change a < 2 ^ 64 at ha
    change a % 8 = 0 at hal
    change 64 * k + 2 * l + j < P.extra_topk at hj'
    change isExtraBlock b d.len0 = true at htag
    have hp : 0 < P.extra_topk := by omega
    have hmem := hpre.extraIdxInput.resolve_left (by omega)
    have hobs := hword a hbits ha hal
    refine ⟨_, bs, hobs.1, .extraIndices hp ⟨rfl, by dsimp [a]; omega, ?_⟩, ?_⟩
    · have hWord := rowWord_lt hb hq hj'
      dsimp [a]
      rw [show 4 * P.b * P.s_q * P.extra_topk = 4 * (P.b * P.s_q * P.extra_topk) by ring]
      omega
    change rebuild 3 bs = .ok (b32 (ipat (slotIdx P L g b l j)))
    have hidx : slotIdx P L g b l j = P.extraIdx (eOf L g) (qOf L g) (64 * k + 2 * l + j) := by
      simp [slotIdx, slotIndex, slotPos, ← h0, htag, topkBlock, k, Nat.mul_comm]
    rw [hidx]
    exact rebuild_index_word hX he hobs fun m hm => by
      have hbyte := hmem.2 _ hb _ hq _ hj' m hm
      simpa [a, j, l, ipat, Nat.mul_add, Nat.add_assoc] using hbyte

/-- The words delivered by the two warp shuffles in each block. -/
def ValidInput (P : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  match d.site with
  | .quad1 _ => ∀ m a b c recv ok, e.kind = .shfl m a b c recv ok →
      ok = true ∧ recv = b32 (laneWord P L g d.block (laneOf L g ^^^ 1))
  | .quad2 _ => ∀ m a b c recv ok, e.kind = .shfl m a b c recv ok →
      ok = true ∧ recv = b32 (pairWord P L g d.block (laneOf L g ^^^ 2))
  | _ => True

private theorem kept_of_next {g : Nat} {d : D} {e : Event}
    (h : next P L g d e ≠ some none ∨ d.site = .barrier) :
    Machine.next P L g (.index d) e ≠ some none := by
  simp only [Machine.next]
  split
  · simp
  · rename_i he
    rcases h with hn | hd
    · exact (hn he).elim
    · simp [hd]
  · simp

/-- The role keeps following its firing events when the two shuffles deliver the partner words.
The launch read-only rule fixes the optional lengths and the initial and prefetched index pairs. -/
theorem next_tracked_of_input {X : Execution} {g i : Nat} {d : D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hs : (Machine.machine P L g).Sound) (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.index d)))
    (hinput : ValidInput P L g d e) :
    Machine.next P L g (.index d) e ≠ some none := by
  apply kept_of_next
  obtain ⟨o, hf⟩ := RingEvents.fired_of_trace hX hs he hd
  cases o with
  | none =>
    cases hs : d.site
    case barrier => exact .inr rfl
    all_goals
      left
      obtain ⟨_, _, hFire⟩ := hf
      rcases fires_none_ends hFire with ⟨f, hk⟩ | hk <;>
        simp [next, nextSite, hs, hk]
  | some u =>
    have hb : eOf L g < P.b := Wg1Mma.eOf_lt_b hpre
    have binding := lengthBindings_of_trace hX hs (by rw [he]; simp) hd
    cases hsite : d.site
    case barrier => exact .inr rfl
    case lenOrig =>
      left
      obtain ⟨ptr, hp⟩ := binding.1 hsite
      obtain ⟨bs, hk, hnc⟩ := main_length hpre hb hp hsite hf
      have hv := LaunchReads.rebuild_main (g := g) hpre hX hb hp he ⟨hk, hnc⟩
      simp [next, nextSite, hsite, hk, hv, Wg0.eOf, eOf]
    case lenExtra =>
      left
      obtain ⟨ptr, hp⟩ := binding.2 hsite
      obtain ⟨bs, hk, hnc⟩ := extra_length hpre hb hp hsite hf
      have hv := LaunchReads.rebuild_extra (g := g) hpre hX hb hp he ⟨hk, hnc⟩
      simp [next, nextSite, hsite, hk, hv, Wg0.eOf, eOf]
    case pair extra first hi =>
      left
      obtain ⟨a, bs, hk, _, hv⟩ := pair_rebuild hpre hX he hsite hf
      simp [next, nextSite, hsite, hk, hv]
    case waitFree extra =>
      left
      cases hk : e.kind <;> simp [next, nextSite, hsite, hk]
    case quad1 extra =>
      left
      cases hk : e.kind <;> simp [next, nextSite, hsite, hk]
      rename_i m a b c recv ok
      have hv := (show ∀ m a b c recv ok, e.kind = .shfl m a b c recv ok → _ by
        simpa only [ValidInput, hsite] using hinput) m a b c recv ok hk
      simp [hv.1, hv.2]
    case quad2 extra =>
      left
      cases hk : e.kind <;> simp [next, nextSite, hsite, hk]
      rename_i m a b c recv ok
      have hv := (show ∀ m a b c recv ok, e.kind = .shfl m a b c recv ok → _ by
        simpa only [ValidInput, hsite] using hinput) m a b c recv ok hk
      simp [hv.1, hv.2]
    case ready extra =>
      left
      cases hk : e.kind <;> simp [next, nextSite, hsite, hk]
    case coord extra hi =>
      left
      cases extra
      · have hc := (congrArg (fun s : Site => kernel.code[s.pc]?) hsite).trans Flow.code_2471
        obtain ⟨t, hat, hinv, hf⟩ := fired_site hf hc
        obtain ⟨a, hk, hl, hsz, _⟩ := fires_coord_main hpre hsite hinv hat hc hf
        simp [next, nextSite, hsite, hk, hl, hsz]
      · have hc := (congrArg (fun s : Site => kernel.code[s.pc]?) hsite).trans Flow.code_2560
        obtain ⟨t, hat, hinv, hf⟩ := fired_site hf hc
        obtain ⟨a, hk, hl, hsz, _⟩ := fires_coord_extra hpre hsite hinv hat hc hf
        simp [next, nextSite, hsite, hk, hl, hsz]
    case valid extra =>
      left
      cases extra
      · have hc := (congrArg (fun s : Site => kernel.code[s.pc]?) hsite).trans Flow.code_2474
        obtain ⟨t, hat, hinv, hf⟩ := fired_site hf hc
        obtain ⟨a, hk, hl, hsz, _⟩ := fires_valid_main hpre hsite hinv hat hc hf
        simp [next, nextSite, hsite, hk, hl, hsz]
      · have hc := (congrArg (fun s : Site => kernel.code[s.pc]?) hsite).trans Flow.code_2563
        obtain ⟨t, hat, hinv, hf⟩ := fired_site hf hc
        obtain ⟨a, hk, hl, hsz, _⟩ := fires_valid_extra hpre hsite hinv hat hc hf
        simp [next, nextSite, hsite, hk, hl, hsz]

/-- The index producer reads its exact current length or index word from a global input array. -/
theorem nc_input_footprint {X : Execution} {g i : Nat} {d : D} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (hSound : (Machine.machine P L g).Sound) (he : X.get (g, i) = some e)
    (hState : Frame.stateAt (Machine.code P L) X g i = some (some (.index d)))
    (hSite : d.site = .lenOrig ∨ d.site = .lenExtra ∨
      ∃ extra first hi, d.site = .pair extra first hi) :
    NcInputEvent P e := by
  intro a bs hk
  have hb := Wg1Mma.eOf_lt_b (g := g) hpre
  obtain ⟨o, hFire⟩ := RingEvents.fired_of_trace hX hSound he hState
  cases o with
  | none =>
    obtain ⟨_, _, hf⟩ := hFire
    rcases fires_none_ends hf with ⟨_, h⟩ | h <;> rw [hk] at h <;> cases h
  | some u =>
    have hBinding := lengthBindings_of_trace hX hSound (by simp [he]) hState
    rcases hSite with hSite | hSite | ⟨extra, first, hi, hSite⟩
    · obtain ⟨ptr, hp⟩ := hBinding.1 hSite
      obtain ⟨_, hRead⟩ := main_length hpre hb hp hSite hFire
      exact NcInputEvent.mainLength hp hb hRead.1 a bs hk
    · obtain ⟨ptr, hp⟩ := hBinding.2 hSite
      obtain ⟨_, hRead⟩ := extra_length hpre hb hp hSite hFire
      exact NcInputEvent.extraLength hp hb hRead.1 a bs hk
    · obtain ⟨a', _, hRead, hRange, _⟩ := pair_rebuild hpre hX he hSite hFire
      cases (Kind.nc.inj (hRead.symm.trans hk)).1
      exact hRange

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1Index
