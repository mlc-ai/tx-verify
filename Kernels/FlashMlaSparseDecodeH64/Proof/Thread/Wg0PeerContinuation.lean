-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerPayload
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerRead
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0Tracking
import Lemmas.Flow.FloatRead

@[expose] public section

/-! # The two peer vector elements and their computed scores -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0

open PTX PTX.Flow PTX.Proof PTX.Assumption

noncomputable section

variable {P : Params} {L : Launch} {g : Nat}

/-- The two loaded QK halves are the FP32 real values of the MMA result. -/
def RealScores (words : List Value) : Prop :=
  ∀ j < 32, ∃ x : ℝ, words.getD j (b32 0) = .float .f32 x

/-- A computed pair consists of two real scores or the negative-infinity mask. -/
def MaskedPair (v : Value) : Prop :=
  ∃ a b : WithBot ℝ, v = .pair (peakVal a) (peakVal b)

/-- Once a peer group's first element has fired, its pending word contains two real scores. -/
def RealPair (v : Value) : Prop :=
  ∃ a b : ℝ, v = .pair (.float .f32 a) (.float .f32 b)

/-- Actual peer exchange payloads preserve finite real scores from Tensor Memory. -/
theorem peerReadValue_real {q : D} (h : RealScores q.peerScores) (j : Fin 8)
    {sub : Nat} (hs : sub < 2) : RealPair (peerReadValue q j.val sub) := by
  have hj := j.isLt
  obtain ⟨a, ha⟩ := h (4 * j.val + 2 * sub) (by omega)
  obtain ⟨b, hb⟩ := h (4 * j.val + 2 * sub + 1) (by omega)
  refine ⟨a, b, ?_⟩
  rw [peerReadValue, ha, hb]
  rfl

private theorem read_masked_pair (m n : Bool) (a b : ℝ) :
    pairRead (joinValue (if m then .float .f32 a else negInf)
      (if n then .float .f32 b else negInf)) =
      some (.ok (if m then (a : EReal) else ⊥, if n then (b : EReal) else ⊥)) := by
  cases m <;> cases n <;> rfl

private theorem add_masked (m : Bool) (a b : ℝ) :
    addEReal (if m then (a : EReal) else ⊥) (b : EReal) =
      some (if m then ((a + b : ℝ) : EReal) else ⊥) := by
  cases m <;> simp [addEReal, EReal.coe_add]

private theorem masked_value (m : Bool) (a : ℝ) :
    erealValue .f32 (if m then (a : EReal) else ⊥) = peakVal (if m then ↑a else ⊥) := by
  cases m
  · rfl
  · exact erealValue_coe .f32 a

/-- The packed add accepts real QK fragments and preserves a negative-infinity mask. -/
theorem peerAdd_masked {d : D} (h : RealScores d.ownScores) {i : Nat} (hi : i < 16)
    {word : Value} (hw : RealPair word) :
    ∃ out, peerAddE (ownScorePair d i) word = .ok out ∧ MaskedPair out := by
  obtain ⟨a, ha⟩ := h (2 * i) (by omega)
  obtain ⟨b, hb⟩ := h (2 * i + 1) (by omega)
  obtain ⟨x, y, rfl⟩ := hw
  let m := d.maskWord.toNat.testBit (2 * i)
  let n := d.maskWord.toNat.testBit (2 * i + 1)
  refine ⟨_, ?_, ⟨if m then ↑(a + x) else ⊥, if n then ↑(b + y) else ⊥, rfl⟩⟩
  rw [ownScorePair, ownMaskedValue, ownMaskedValue, ha, hb]
  have hp := read_masked_pair true true x y
  change pairRead (.pair (.float .f32 x) (.float .f32 y)) =
    some (.ok ((x : EReal), (y : EReal))) at hp
  simp only [peerAddE, idealAdd2, read_masked_pair, hp, bindRead, add_masked,
    masked_value, pure, Except.pure, m, n]

private def scoreReal : WithBot ℝ → EReal
  | ⊥ => ⊥
  | some x => (x : EReal)

private theorem read_peak (s : WithBot ℝ) :
    readEReal .f32 (peakVal s) = some (.ok (scoreReal s)) := by
  cases s
  · rfl
  · exact readEReal_of_valFloat valFloat_float

private theorem encode_peak (s : WithBot ℝ) :
    erealValue .f32 (scoreReal s) = peakVal s := by
  cases s
  · rfl
  · exact erealValue_coe _ _

private theorem scoreReal_max (a b : WithBot ℝ) :
    max (scoreReal a) (scoreReal b) = scoreReal (max a b) := by
  cases a with
  | bot => cases b <;> simp [scoreReal]
  | coe a =>
    cases b with
    | bot => simp [scoreReal]
    | coe b =>
      rw [← WithBot.coe_max]
      exact coe_max

/-- Comparing two canonical row peaks preserves the finite-or-masked representation. -/
theorem peerMaxE_peak (a b : WithBot ℝ) :
    peerMaxE (peakVal a) (peakVal b) = .ok (peakVal (max a b)) := by
  simp [peerMaxE, idealMax, read_peak, bindRead, scoreReal_max, encode_peak, pure, Except.pure]

private theorem unpack_masked (a b : WithBot ℝ) :
    unpackE 64 (.pair (peakVal a) (peakVal b)) = .ok (peakVal a, peakVal b) := by
  cases a <;> cases b <;> rfl

theorem peakVal_eq_negInf {m : WithBot ℝ} : peakVal m = negInf ↔ m = ⊥ := by
  cases m <;> simp [peakVal, negInf]

private theorem masked_peak_bot (a b : WithBot ℝ) :
    .pair (peakVal a) (peakVal b) = Value.pair negInf negInf ↔ a = ⊥ ∧ b = ⊥ := by
  simp [peakVal_eq_negInf]

private theorem fold_max {words : Nat → Value} (base : Nat) (ks : List Nat)
    (h : ∀ i ∈ ks, MaskedPair (words (base + i + 1))) (z : WithBot ℝ) :
    ∃ out : WithBot ℝ, ks.foldlM (fun acc i => do
      let (a, b) ← unpackE 64 (words (base + i + 1))
      let acc ← peerMaxE acc a
      peerMaxE acc b) (peakVal z) = .ok (peakVal out) ∧
      (out = ⊥ ↔ z = ⊥ ∧ ∀ i ∈ ks, words (base + i + 1) = .pair negInf negInf) := by
  induction ks generalizing z with
  | nil => exact ⟨z, rfl, by simp⟩
  | cons k ks ih =>
    obtain ⟨a, b, hab⟩ := h k (by simp)
    have hks : ∀ i ∈ ks, MaskedPair (words (base + i + 1)) :=
      fun i hi => h i (List.mem_cons_of_mem k hi)
    obtain ⟨out, hfold, hBot⟩ := ih hks (max (max z a) b)
    refine ⟨out, ?_, ?_⟩
    · simpa only [List.foldlM_cons, hab, unpack_masked, peerMaxE_peak, bind, Except.bind]
        using hfold
    · rw [hBot, max_eq_bot, max_eq_bot, List.forall_mem_cons, hab, masked_peak_bot]
      tauto

private theorem half_max {words : Nat → Value} (base : Nat)
    (h : ∀ i < 8, MaskedPair (words (base + i))) :
    ∃ out : WithBot ℝ, peerHalfMax words base = .ok (peakVal out) ∧
      (out = ⊥ ↔ ∀ i < 8, words (base + i) = .pair negInf negInf) := by
  obtain ⟨a, b, hab⟩ := h 0 (by decide)
  have hf : ∀ i ∈ List.range 7, MaskedPair (words (base + i + 1)) := by
    intro i hi
    rw [Nat.add_assoc]
    exact h (i + 1) (by have := List.mem_range.mp hi; omega)
  obtain ⟨out, hfold, hBot⟩ := fold_max base (List.range 7) hf (max (max a ⊥) b)
  refine ⟨out, ?_, ?_⟩
  · rw [Nat.add_zero] at hab
    have hzero : b32 4286578688 = peakVal ⊥ := rfl
    simpa only [peerHalfMax, hab, unpack_masked, hzero, peerMaxE_peak, bind, Except.bind]
      using hfold
  · rw [hBot, max_bot_right, max_eq_bot, ← masked_peak_bot, ← hab]
    constructor
    · intro ⟨h0, hRest⟩ i hi
      by_cases hz : i = 0
      · simpa only [hz] using h0
      · have he := hRest (i - 1) (List.mem_range.mpr (by omega))
        rwa [show base + (i - 1) + 1 = base + i by omega] at he
    · intro hAll
      refine ⟨hAll 0 (by decide), ?_⟩
      intro i hi
      rw [Nat.add_assoc]
      exact hAll (i + 1) (by have := List.mem_range.mp hi; omega)

private theorem scale_read {mem0 : Mem0} (hpre : Pre P L mem0) :
    readEReal .f32 (b32 (paramWord L 28 4)) = some (.ok (P.scale : EReal)) := by
  apply readEReal_of_valFloat
  let n := paramWord L 28 4
  obtain ⟨w, _, hbytes, _⟩ := hpre.paramScale
  have hr := Thread.paramWord_four (L := L) (off := 28) (x := w)
    (fun j hj => by simpa using hbytes j hj)
  have hn : n < 2 ^ 32 := by
    change Thread.paramWord L 28 4 = w % 2 ^ 32 at hr
    change Thread.paramWord L 28 4 < 2 ^ 32
    rw [hr]
    exact Nat.mod_lt _ (by decide)
  have hb : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hn.trans (by decide))]
  change bitsAsFloat .f32 (b32 n) = .ok P.scale
  rw [bitsAsFloat_eq (by intro f hf; cases hf)]
  simp only [b32, Value.bitPattern, Value.bytes, FloatFmt.bytes, Nat.reduceDiv, hb, ↓reduceIte]
  obtain ⟨x, hx, he⟩ := Option.map_eq_some_iff.mp (scaleWord hpre)
  change FloatFmt.f32.decode n = some x at hx
  simp [hx, he, pure, Except.pure]

private theorem mul_peak {mem0 : Mem0} (hpre : Pre P L mem0) (a : WithBot ℝ) :
    ∃ out : WithBot ℝ, mulE true (peakVal a) (b32 (paramWord L 28 4)) = .ok (peakVal out) ∧
      (out = ⊥ ↔ a = ⊥) := by
  rw [mulE, idealMul, read_peak, scale_read hpre]
  cases a with
  | bot =>
    refine ⟨⊥, ?_, Iff.rfl⟩
    have hn : (P.scale : EReal) ≠ 0 := (EReal.coe_pos.mpr hpre.scalePos).ne'
    simpa [scoreReal, bindRead, mulEReal, hn, pure, Except.pure,
      EReal.bot_mul_coe_of_pos hpre.scalePos] using encode_peak ⊥
  | coe a =>
    refine ⟨↑(a * P.scale), ?_, iff_of_false WithBot.coe_ne_bot WithBot.coe_ne_bot⟩
    simp only [scoreReal, bindRead, mulEReal_coe, Option.map_some, pure, Except.pure,
      erealValue_coe, peakVal]

private theorem peerRowMax_peak {mem0 : Mem0} (hpre : Pre P L mem0) {words : Nat → Value}
    (h : ∀ i < 16, MaskedPair (words i)) :
    ∃ out : WithBot ℝ, peerRowMax words (b32 (paramWord L 28 4)) = .ok (peakVal out) ∧
      (out = ⊥ ↔ ∀ i < 16, words i = .pair negInf negInf) := by
  obtain ⟨a, ha, haBot⟩ := half_max 0 (fun i hi => h (0 + i) (by omega))
  obtain ⟨b, hb, hbBot⟩ := half_max 8 (fun i hi => h (8 + i) (by omega))
  obtain ⟨out, hr, hBot⟩ := mul_peak hpre (max a b)
  refine ⟨out, ?_, ?_⟩
  · simpa only [peerRowMax, ha, hb, bind, Except.bind, peerMaxE_peak] using hr
  · rw [hBot, max_eq_bot, haBot, hbBot]
    constructor
    · intro ⟨hLo, hHi⟩ i hi
      by_cases h8 : i < 8
      · simpa only [Nat.zero_add] using hLo i h8
      · simpa only [show 8 + (i - 8) = i by omega] using hHi (i - 8) (by omega)
    · intro hAll
      exact ⟨fun i hi => hAll _ (by omega), fun i hi => hAll _ (by omega)⟩

/-- The final local reduction accepts all sixteen completed masked score pairs. -/
theorem peerRowMax_succeeds {mem0 : Mem0} (hpre : Pre P L mem0) {words : Nat → Value}
    (h : ∀ i < 16, MaskedPair (words i)) :
    ∃ out, peerRowMax words (b32 (paramWord L 28 4)) = .ok out := by
  obtain ⟨out, hOut, _⟩ := peerRowMax_peak hpre h
  exact ⟨peakVal out, hOut⟩

/-- The local maximum stored for a completed set of masked pairs is a canonical row peak. -/
theorem rowLocalMax_of_masked {mem0 : Mem0} (hpre : Pre P L mem0) {d : D}
    (h : ∀ i < 16, MaskedPair (d.scoreSums i)) :
    ∃ out : WithBot ℝ, rowLocalMax L d = peakVal out := by
  obtain ⟨out, hOut, _⟩ := peerRowMax_peak hpre h
  exact ⟨out, by simp only [rowLocalMax, hOut, Except.toOption, Option.getD_some]⟩

/-- The lane's local maximum is negative infinity exactly when all sixteen pairs are masked. -/
theorem rowLocalMax_bot_iff {mem0 : Mem0} (hpre : Pre P L mem0) {d : D}
    (h : ∀ i < 16, MaskedPair (d.scoreSums i)) :
    ∃ out : WithBot ℝ, rowLocalMax L d = peakVal out ∧
      (out = ⊥ ↔ ∀ i < 16, d.scoreSums i = .pair negInf negInf) := by
  obtain ⟨out, hOut, hBot⟩ := peerRowMax_peak hpre h
  exact ⟨out, by simp only [rowLocalMax, hOut, Except.toOption, Option.getD_some], hBot⟩

/-- The second element uses one pending pair and the previously completed groups. -/
def PeerPrefix (d : D) (group : Fin 8) : Prop :=
  (d.sub = 1 → ∃ first, d.peerPending = [first] ∧ RealPair first) ∧
    ∀ j < 2 * group.val, MaskedPair (d.scoreSums j)

/-- The first element establishes the pending pair without changing any completed sums. -/
theorem peerPrefix_first {d : D} {group : Fin 8} {word : Value}
    (hp : PeerPrefix d group) (hw : RealPair word) :
    PeerPrefix {d with sub := 1, peerPending := [word]} group :=
  ⟨fun _ => ⟨word, rfl, hw⟩, hp.2⟩

/-- Inverting the actual load event supplies both pieces of access geometry and its sub-index. -/
theorem composed_peer_geometry {mem0 : Mem0} (hpre : Pre P L mem0)
    {d : D} {e : Event} {u : TState} {group : Fin 8} (hd : d.site = .peerRead group)
    (hf : (Machine.machine P L g).Fired (some (.wg0 d)) e (some u)) :
    ∃ a bs, e.kind = .rd a bs ∧ siteLoc L g d.site d.block d.sub = some a.loc ∧
      a.size = 8 ∧ d.sub < 2 := by
  have hf' : (Wg0.code P L g).toMachine.Fired (some d) e (some u) := hf
  obtain ⟨t, ht, hf'⟩ := hf'
  change (Wg0.code P L g).AtD d t ∧ Inv P L g d at ht
  obtain ⟨ins, hc, _, _⟩ := site_event P L g d
  change Fires t.pc (match kernel.code[d.site.pc]? with
    | some ins => eventTmpl asms L g t ins.op
    | none => .ub .pcOutOfRange) e (some u) at hf'
  rw [ht.1.1, hc] at hf'
  obtain ⟨a, bs, he, ha, hz, _⟩ := fires_peerRead_at hpre hd ht.2 ht.1 hc hf'
  exact ⟨a, bs, he, ha, by simpa only [hd, Site.elemBytes] using hz,
    by simpa only [hd, Site.elems] using ht.2.subLt⟩

/-- The first element's successful reconstruction becomes the exact pending word. -/
theorem composed_peerFirst_ready {d : D} {e : Event} {group : Fin 8}
    {a : Acc} {bs : List (Option Byte)} {word : Value}
    (hd : d.site = .peerRead group) (hsub : d.sub = 0)
    (he : e.kind = .rd a bs) (haddr : siteLoc L g d.site d.block d.sub = some a.loc)
    (hz : a.size = 8) (hw : rebuild 3 bs = .ok word) :
    Machine.next P L g (.wg0 d) e =
      some (some (.wg0 {d with sub := 1, peerPending := [word]})) := by
  rw [hd, hsub] at haddr
  simp [Machine.next, Wg0.next, nextSite, hd, he, haddr, hz, hw, hsub, Site.elemBytes]

/-- A matching second element completes two masked sums and advances to the next group
or the local-row-maximum write. -/
theorem composed_peerSecond_next {mem0 : Mem0} (hpre : Pre P L mem0)
    {d : D} {e : Event} {group : Fin 8} {a : Acc} {bs : List (Option Byte)} {word : Value}
    (hd : d.site = .peerRead group) (hsub : d.sub = 1)
    (he : e.kind = .rd a bs) (haddr : siteLoc L g d.site d.block d.sub = some a.loc)
    (hz : a.size = 8) (hw : rebuild 3 bs = .ok word)
    (hown : RealScores d.ownScores) (hp : PeerPrefix d group) (hwReal : RealPair word) :
    ∃ d', Machine.next P L g (.wg0 d) e = some (some (.wg0 d')) ∧
      d'.block = d.block ∧ d'.sub = 0 ∧
      ((∃ nextGroup : Fin 8, d'.site = .peerRead nextGroup ∧
          nextGroup.val = group.val + 1 ∧ PeerPrefix d' nextGroup) ∨
        (d'.site = .rowMax ∧ group.val = 7 ∧ ∀ j < 16, MaskedPair (d'.scoreSums j))) := by
  have hlt := group.isLt
  rw [hd, hsub] at haddr
  obtain ⟨first, hpending, hf⟩ := hp.1 hsub
  let k := 2 * group.val
  obtain ⟨left, hleft, hL⟩ := peerAdd_masked hown (i := k) (by dsimp [k]; omega) hf
  obtain ⟨right, hright, hR⟩ := peerAdd_masked hown (i := k + 1) (by dsimp [k]; omega) hwReal
  let sums := Function.update (Function.update d.scoreSums k left) (k + 1) right
  have hmask j (hj : j < k + 2) : MaskedPair (sums j) := by
    by_cases h : j = k + 1
    · subst j
      simpa [sums] using hR
    by_cases h' : j = k
    · subst j
      simpa [sums, Function.update_of_ne (show k ≠ k + 1 by omega)] using hL
    simpa only [sums, Function.update_of_ne h, Function.update_of_ne h'] using hp.2 j (by omega)
  let bare : D := { d with sub := 0, peerPending := [], scoreSums := sums }
  by_cases hnext : group.val + 1 < 8
  · let nextGroup : Fin 8 := ⟨group.val + 1, hnext⟩
    let d' := { bare with site := Site.peerRead nextGroup }
    refine ⟨d', ?_, rfl, rfl, .inl ⟨nextGroup, rfl, rfl, ?_⟩⟩
    · simp [Machine.next, Wg0.next, nextSite, hd, he, haddr, hz, hw, hsub, hpending, Site.elemBytes,
        hleft, hright, hnext, d', bare, nextGroup, sums, k]
    exact ⟨by simp [d', bare], fun j hj => hmask j (by dsimp [nextGroup, k] at *; omega)⟩
  · have hall j (hj : j < 16) : MaskedPair (sums j) := hmask j (by dsimp [k]; omega)
    obtain ⟨_, hrow⟩ := peerRowMax_succeeds hpre hall
    let d' := { bare with site := Site.rowMax }
    refine ⟨d', ?_, rfl, rfl, .inr ⟨rfl, by omega, hall⟩⟩
    simp [Machine.next, Wg0.next, nextSite, hd, he, haddr, hz, hw, hsub, hpending, Site.elemBytes,
      hleft, hright, hnext, hrow, d', bare, sums, k, Except.toOption]

set_option maxHeartbeats 1500000 in
private theorem peer_entry_role {d d' : D} {e : Event} {group : Fin 8}
    (hn : Wg0.next P L g d e = some (some d'))
    (hsite : d'.site = .peerRead group) (hsource : ∀ j, d.site ≠ .peerRead j) :
    d.site = .pairBar ∧ group = 0 ∧ d'.sub = d.sub := by
  cases hd : d.site <;>
    simp only [Wg0.next, nextSite, writeStep, waitStep, hd] at hn
  case peerRead j => exact (hsource j hd).elim
  case maxRead =>
    split at hn
    · split at hn
      · obtain ⟨_, _, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
        obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp hmap
        cases hsite
      · cases hn
    · cases hn
  case rescaleVote =>
    split at hn
    · obtain ⟨voted, hv, hmap⟩ := Option.bind_eq_some_iff.mp (Option.some.inj hn)
      obtain ⟨updated, hp, rfl⟩ := Option.map_eq_some_iff.mp hmap
      cases hsite
    · cases hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals simp_all [afterScoreSite, afterLen, afterSink, epiAfterBar, loadScores, init]
  all_goals split_ifs at hsite

/-- An actual transition entering a peer read from another site must have passed the pair barrier.
A transition within the peer exchange is identified separately. -/
theorem composed_peer_predecessor {d' : D} {e : Event} {s : Machine.ThreadD} {group : Fin 8}
    (hn : Machine.next P L g s e = some (some (.wg0 d'))) (hsite : d'.site = .peerRead group) :
    ∃ d : D, s = .wg0 d ∧
      ((d.site = .pairBar ∧ group = 0 ∧ d'.sub = d.sub) ∨ ∃ j, d.site = .peerRead j) := by
  cases s with
  | wg0 d =>
    refine ⟨d, rfl, ?_⟩
    by_cases hex : ∃ j, d.site = .peerRead j
    · exact .inr hex
    · apply Or.inl
      simp only [Machine.next] at hn
      split at hn
      · rename_i q hq
        cases hn
        exact peer_entry_role hq hsite (fun j hj => hex ⟨j, hj⟩)
      · split_ifs at hn <;> cases hn
      · cases hn
  | prologue s =>
    simp only [Machine.next] at hn
    split at hn
    · cases hn
    · split at hn
      · rename_i w _
        split_ifs at hn
        · fin_cases w <;> cases hn
          unfold init firstSite afterSink afterLen at hsite
          dsimp only at hsite
          split_ifs at hsite
        · cases hn
      · cases hn
    · cases hn
  | head =>
    cases hk : e.kind <;> simp only [Machine.next, hk, reduceCtorEq] at hn
    simp only [Machine.headStart] at hn
    split_ifs at hn <;> cases hn
  | _ =>
    simp only [Machine.next] at hn
    repeat' split at hn
    all_goals cases hn

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
