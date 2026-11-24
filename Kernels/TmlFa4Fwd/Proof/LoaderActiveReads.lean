-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderActiveEntry
public import Kernels.TmlFa4Fwd.Proof.ResultGeometry
public import Kernels.TmlFa4Fwd.Proof.LoaderPrefixDemand
public import Kernels.TmlFa4Fwd.Flow.Code.Part005
public import Kernels.TmlFa4Fwd.Flow.Code.Part006

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- The exact scalar load of an active loader site, before making any progress claim. -/
theorem loaderWordReadNext {l : Launch} {g pc base off ra rd : Nat}
    {t : TState} {F : List (Nat × Value)}
    (hLo : 174 ≤ pc) (hHi : pc < 1906)
    (hCode : kernel.code[pc]? = some ⟨none, .mem
      { kind := .load, space := some .global, sem := .weak, elem := .int .b 32,
        addr := ⟨.reg ra 64, Int.ofNat off⟩, dsts := [some rd] }⟩)
    (ht : At t pc F) (hPtr : t.regs ra = some (b64 base))
    (hFit : base + off < 2 ^ 64) (hAlign : (base + off) % 4 = 0) :
    Next kernel Assumptions.all l g t t
      (.read {loc := globalLoc (base+off),size := 4} (afterLoad t [rd])) := by
  let acc : Acc := {loc := globalLoc (base + off), size := 4}
  have hBase : base < 2 ^ 64 := by omega
  have hEff : effAddr l g t .global ra (Int.ofNat off) = .ok acc.loc := by
    simp only [effAddr, readBits_b64 hPtr hBase, bind, Except.bind, pure, Except.pure,
      acc, globalLoc]
    change (Except.ok (⟨.global, 0,
      (BitVec.ofNat 64 base + BitVec.ofInt 64 (off : Int)).toNat⟩ : Loc)) = _
    rw [BitVec.ofInt_natCast, ← BitVec.ofNat_add, toNat_ofNat_lt hFit]
  have hOut : out kernel Assumptions.all l g t = .ev (.read acc (afterLoad t [rd])) := by
    rw [loaderOutCore (by rw [ht.1]; exact hLo) (by rw [ht.1]; exact hHi)]
    rw [out_event ht.2.2.2.1 (by rw [ht.1]; exact hCode) rfl rfl]
    change Out.ev (loadTmpl [] l g t .global false 32 [rd] ra (Int.ofNat off)) = _
    unfold loadTmpl
    rw [hEff]
    simp only [bind, Except.bind, ht.2.1, List.length_singleton]
    rw [elemAcc_ok (loc := acc.loc) (n := 4) (count := 1) (j := 0)
      (by decide) (show acc.loc.addr % (4 * 1) = 0 from hAlign)]
    rfl
  exact ⟨.refl,hOut⟩

private theorem wordRead {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g i pc base off ra rd value : Nat} {t : TState} {F : List (Nat × Value)}
    (hLo : 174 ≤ pc) (hHi : pc < 1906)
    (hCode : kernel.code[pc]? = some ⟨none, .mem
      { kind := .load, space := some .global, sem := .weak, elem := .int .b 32,
        addr := ⟨.reg ra 64, Int.ofNat off⟩, dsts := [some rd] }⟩)
    (ht : At t pc F) (hPtr : t.regs ra = some (b64 base))
    (hFit : base + off < 2 ^ 64) (hAlign : (base + off) % 4 = 0)
    (hValue : HasValue m (globalLoc (base + off)) (b32 value))
    (hFree : ∀ k < 4, ∀ w a data, X.MemWrites w a data →
      ¬ a.Covers ((globalLoc (base + off)).at k))
    (hFresh : ∀ pair ∈ F, pair.1 ≠ rd)
    {ending : Option TState}
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop i) ending)
    (hMore : (X.tr g).drop i ≠ []) :
    ∃ u, X.get (g, i) =
        some ⟨pc, .rd {loc := globalLoc (base + off), size := 4} ((b32 value).toBytes.map some)⟩ ∧
      At u (pc + 1) ((rd, b32 value) :: F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (i + 1)) ending := by
  let acc : Acc := {loc := globalLoc (base + off), size := 4}
  have hn := loaderWordReadNext (l := l) (g := g) hLo hHi hCode ht hPtr hFit hAlign
  obtain ⟨_, _, he, ⟨bs, _, rfl, hCont⟩, hTail⟩ := hn.continuing_at_nonempty (by
    rintro e ⟨_, _, _, hBad⟩
    cases hBad) hr hMore
  obtain rfl := Option.some.inj hCont
  rw [ht.1] at he
  have hh : X.MemReads (.thread (g, i)) acc bs := .inl ⟨pc, he⟩
  have hBs : bs = (b32 value).toBytes.map some := by
    apply hX.launch_value hh rfl hFree
    exact hValue
  subst bs
  have hR := PTX.Proof.rebuild_scalar (v := b32 value) (show 0 < 4 by decide) rfl
  have hAfter : afterLoad t [rd] ((b32 value).toBytes.map some) =
      next (setReg t rd (b32 value)) := by
    rw [afterLoad_ok ht.2.1 ht.2.2.1 hR]
    simp [next, setReg, ht.2.1, ht.2.2.1]
  rw [hAfter] at hTail
  exact ⟨_, he, ht.set hFresh, hTail⟩

/-- Read the first active request CuQ word from a nonempty suffix. -/
theorem activeFirstCuQRead {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i batch : Nat} (hb : batch < p.batch) {t : TState} {F : List (Nat × Value)}
    (ht : At t 381 F) (hPtr : t.regs 7515 = some (b64 (p.cuQBase + 4 * batch)))
    (hFree : ∀ k < 4, ∀ w a data, X.MemWrites w a data →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * batch)).at k))
    (hFresh : ∀ x ∈ F, x.1 ≠ 1799) {ending : Option TState}
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop i) ending)
    (hMore : (X.tr g).drop i ≠ []) :
    ∃ u, X.get (g, i) = some ⟨381,
        .rd {loc := globalLoc (p.cuQBase + 4 * batch), size := 4}
          ((b32 (p.qOffset batch)).toBytes.map some)⟩ ∧
      At u 382 ((1799, b32 (p.qOffset batch)) :: F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (i + 1)) ending := by
  have hRange := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hRange
  have hAlign := hp.alignment.2.2.2.2.2.2.2.2.1
  exact wordRead hX (off := 0) (by decide) (by decide) Flow.code_381 ht hPtr (by omega)
    (by omega) (hp.cuQ batch hb.le) hFree hFresh hr hMore

/-- Read the second active request CuQ word from a nonempty suffix. -/
theorem activeSecondCuQRead {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i batch : Nat} (hb : batch < p.batch) {t : TState} {F : List (Nat × Value)}
    (ht : At t 382 F) (hPtr : t.regs 7515 = some (b64 (p.cuQBase + 4 * batch)))
    (hFree : ∀ k < 4, ∀ w a data, X.MemWrites w a data →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * (batch + 1))).at k))
    (hFresh : ∀ x ∈ F, x.1 ≠ 1800) {ending : Option TState}
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop i) ending)
    (hMore : (X.tr g).drop i ≠ []) :
    ∃ u, X.get (g, i) = some ⟨382,
        .rd {loc := globalLoc (p.cuQBase + 4 * (batch + 1)), size := 4}
          ((b32 (p.qOffset (batch + 1))).toBytes.map some)⟩ ∧
      At u 383 ((1800, b32 (p.qOffset (batch + 1))) :: F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (i + 1)) ending := by
  have hRange := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hRange
  have hAlign := hp.alignment.2.2.2.2.2.2.2.2.1
  have hEq : p.cuQBase + 4 * batch + 4 = p.cuQBase + 4 * (batch + 1) := by omega
  obtain ⟨u, he, hu, hTail⟩ := wordRead hX (off := 4) (by decide) (by decide) Flow.code_382 ht
    hPtr (by omega) (by omega) (by rw [hEq]; exact hp.cuQ _ (by omega))
    (by rw [hEq]; exact hFree) hFresh hr hMore
  exact ⟨u, by rwa [hEq] at he, hu, hTail⟩

/-- The active loader computes the selected request's used-K pointer after the two CuQ reads. -/
theorem activeUsedKAddress {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g batch : Nat} (hb : batch < p.batch) :
    Seg kernel [] l g 2 383 [(1799, b32 (p.qOffset batch)), (1800, b32 (p.qOffset (batch + 1))),
      (7503, b64 p.usedKBase), (7514, b64 (4 * batch))] 385
      [(7516, b64 (p.usedKBase + 4 * batch)),
       (1085, b32 ((2 ^ 32 - p.qLength batch) % 2 ^ 32))] := by
  have hRange := hp.ranges ⟨p.usedKBase, 4 * p.batch⟩ (by simp [Params.inputRegions])
  change p.usedKBase + 4 * p.batch ≤ 2 ^ 64 at hRange
  have hTotal := hp.shape.2.2.2.2.2
  have hLoQ := hp.qOffset_le_total hb.le
  have hHiQ := hp.qOffset_le_total (show batch + 1 ≤ p.batch by omega)
  have hMonotone := (hp.lengths batch hb).1
  have hLo : p.qOffset batch < 2 ^ 32 := by omega
  have hHi : p.qOffset (batch + 1) < 2 ^ 32 := by omega
  have hWrap : (18446744073709551616 - p.qOffset (batch + 1) + p.qOffset batch)
        % 18446744073709551616 % 2 ^ 32 =
      (2 ^ 32 - p.qLength batch) % 2 ^ 32 := by
    rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ 32 ∣ 18446744073709551616)]
    unfold Params.qLength
    omega
  have hHi64 : p.qOffset (batch + 1) < 18446744073709551616 := by omega
  have hWord :
      truncBits 32 (BitVec.ofNat 64 (p.qOffset batch) -
        BitVec.ofNat 64 (p.qOffset (batch + 1))) =
      BitVec.ofNat 64 ((2 ^ 32 - p.qLength batch) % 2 ^ 32) := by
    rw [nf_sub, Nat.mod_eq_of_lt hHi64, nf_trunc, hWrap]
  intro t ht
  seg_fp ht using
    first
    | simp only [b64, truncBits_ofNat (show p.usedKBase < 2 ^ 64 by omega) (by decide),
        truncBits_ofNat (show 4 * batch < 2 ^ 64 by omega) (by decide), ← BitVec.ofNat_add,
        truncBits_ofNat (show p.usedKBase + 4 * batch < 2 ^ 64 by omega) (by decide)]
    | simp only [b32, truncBits_ofNat hLo (by decide), truncBits_ofNat hHi (by decide), hWord]



/-- Register facts retained across the actual active request metadata reads. -/
structure ActiveReadExtra (G : List (Nat × Value)) : Prop where
  qlo : ∀ x ∈ G, x.1 ≠ 1799
  qhi : ∀ x ∈ G, x.1 ≠ 1800
  used : ∀ x ∈ G, x.1 ≠ 1086
  prep : ((kernel.code.drop 383).take 2).all
    (fun ins => (G.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc) {g i batch tid tile head : Nat}
    (hb : batch < p.batch) {t : TState}
include hp hX writes hb

/-- The active loader reads the two adjacent cuQ offsets and the selected request's used-K
length from their immutable global regions. The events are consecutive in the actual trace. -/
theorem loaderActiveReadWordsFrameInPrefix {G : List (Nat × Value)} (hG : ActiveReadExtra G)
    (ht : At t 381 ((loaderActiveFacts p l tid batch ++
      [(7168, b32 tile), (7169, b32 head), (7170, b32 batch), (7296, b64 16)]) ++ G))
    {ending : Option TState} (hr : Run kernel Assumptions.all l g t ((X.tr g).drop i) ending)
    (hProgress : PrefixDemand X g i 384 ending) :
    ∃ u,
      X.get (g, i) = some ⟨381, .rd {loc := globalLoc (p.cuQBase + 4 * batch), size := 4}
        ((b32 (p.qOffset batch)).toBytes.map some)⟩ ∧
      X.get (g, i + 1) = some ⟨382, .rd {loc := globalLoc (p.cuQBase + 4 * (batch + 1)), size := 4}
        ((b32 (p.qOffset (batch + 1))).toBytes.map some)⟩ ∧
      X.get (g, i + 1 + 1) = some ⟨385, .rd {loc := globalLoc (p.usedKBase + 4 * batch), size := 4}
        ((b32 (p.kLength batch)).toBytes.map some)⟩ ∧
      At u 386 ([(1086, b32 (p.kLength batch)), (1799, b32 (p.qOffset batch)),
        (1800, b32 (p.qOffset (batch + 1))), (1085, b32 ((2 ^ 32 - p.qLength batch) % 2 ^ 32))] ++
        ((loaderActiveFacts p l tid batch ++
          [(7168, b32 tile), (7169, b32 head), (7170, b32 batch), (7296, b64 16)]) ++ G)) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (i + 1 + 1 + 1)) ending := by
  let F := loaderActiveFacts p l tid batch ++
    [(7168, b32 tile), (7169, b32 head), (7170, b32 batch), (7296, b64 16)]
  let base := p.cuQBase + 4 * batch
  let used := p.usedKBase + 4 * batch
  let F₁ := (1799, b32 (p.qOffset batch)) :: (F ++ G)
  let F₂ := (1800, b32 (p.qOffset (batch + 1))) :: (1799, b32 (p.qOffset batch)) :: F
  have hKRange := hp.ranges ⟨p.usedKBase, 4 * p.batch⟩ (by simp [Params.inputRegions])
  change p.usedKBase + 4 * p.batch ≤ 2 ^ 64 at hKRange
  have hKAlign := hp.alignment.2.2.2.2.2.2.2.2.2.1
  have hQ := hp.cuQ_protected writes
  have noReg {A : List (Nat × Value)} {r : Nat} (h : r ∉ A.map Prod.fst) :
      ∀ x ∈ A, x.1 ≠ r := by
    intro x hm he
    exact h (he ▸ List.mem_map_of_mem hm)
  have hPtr : t.regs 7515 = some (b64 base) := ht.2.2.2.2.1
  obtain ⟨v, he, hV, hRun⟩ := activeFirstCuQRead hp hX hb ht hPtr (hQ batch hb.le)
    (by
      intro x hx
      exact (List.mem_append.mp hx).elim
        (noReg (show 1799 ∉ F.map Prod.fst from of_decide_eq_true rfl) x) (hG.qlo x))
    hr (hProgress.nonempty hr)
  have hNext := hProgress.advance he (by change 381 ≤ 384; decide)
  have hPtr' : v.regs 7515 = some (b64 base) := hV.2.2.2.2.2.1
  have hb' : batch + 1 ≤ p.batch := by omega
  obtain ⟨s, he', hS, hRun'⟩ := activeSecondCuQRead hp hX hb hV hPtr' (hQ (batch + 1) hb')
    (by
      intro x hx
      change x ∈ (1799, b32 (p.qOffset batch)) :: F ++ G at hx
      have hc : x ∈ ((1799, b32 (p.qOffset batch)) :: F) ++ G := hx
      exact (List.mem_append.mp hc).elim
        (noReg (show 1800 ∉ (((1799, b32 (p.qOffset batch)) :: F).map Prod.fst) from
          of_decide_eq_true rfl) x) (hG.qhi x)) hRun (hNext.nonempty hRun)
  have hThird := hNext.advance he' (by change 382 ≤ 384; decide)
  have hArgs : At s 383 [(1799, b32 (p.qOffset batch)), (1800, b32 (p.qOffset (batch + 1))),
      (7503, b64 p.usedKBase), (7514, b64 (4 * batch))] := by
    apply hS.mono
    repeat' apply And.intro
    all_goals first | trivial | (apply holds_lookup hS.2.2.2.2; rfl)
  obtain ⟨w, hw, hW⟩ := activeUsedKAddress (g := g) hp hb s hArgs
  have hBaseKeep : ((kernel.code.drop 383).take 2).all
      (fun ins => (F₂.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨hwA, hwFrame⟩ := loaderLinear (regs := (F₂ ++ G).map Prod.fst)
    (by decide) (by decide) hS.1
    (by
      apply List.all_eq_true.mpr
      intro ins hi
      rw [List.map_append, List.all_append, List.all_eq_true.mp hBaseKeep ins hi,
        List.all_eq_true.mp hG.prep ins hi]
      rfl) rfl hw
  have hF₂ : Holds w.regs (F₂ ++ G) := holdsSchedulerFrame hS.2.2.2.2 hwFrame
    (fun _ hm => List.mem_map_of_mem hm)
  let F₃ := (7516, b64 used) :: (1085, b32 ((2 ^ 32 - p.qLength batch) % 2 ^ 32)) :: F₂
  have hAt : At w 385 (F₃ ++ G) := hW.mono ⟨hW.2.2.2.2.1, hW.2.2.2.2.2.1, hF₂⟩
  have hUsed : ∀ k < 4, ∀ w a data, X.MemWrites w a data →
      ¬ a.Covers ((globalLoc used).at k) := by
    intro k hk w a data hWrite
    apply hp.inputByte_unwritten writes (region := ⟨p.usedKBase, 4 * p.batch⟩)
    · simp [Params.inputRegions]
    · exact ⟨rfl, rfl, by dsimp [used, globalLoc, Loc.at]; omega,
        by dsimp [used, globalLoc, Loc.at]; omega⟩
    · exact hWrite
  obtain ⟨u, he'', hU, hRun''⟩ := wordRead hX (off := 0) (by decide) (by decide) Flow.code_385
    hAt hAt.2.2.2.2.1 (by dsimp [used]; omega) (by dsimp [used]; omega)
    (hp.usedK batch hb) hUsed
    (by
      intro x hx
      exact (List.mem_append.mp hx).elim
        (noReg (show 1086 ∉ F₃.map Prod.fst from of_decide_eq_true rfl) x) (hG.used x))
    (hRun'.after_local_nonempty (run_rtg hwA) (hThird.nonempty hRun'))
    (hThird.nonempty hRun')
  exact ⟨u, he, he', he'',
    hU.mono ⟨hU.2.2.2.2.1, hU.2.2.2.2.2.2.2.2.1,
      hU.2.2.2.2.2.2.2.1, hU.2.2.2.2.2.2.1, hU.2.2.2.2.2.2.2.2.2⟩, hRun''⟩

/-- The same metadata fence for a terminated loader trace. -/
theorem loaderActiveReadWordsFrame {G : List (Nat × Value)} (hG : ActiveReadExtra G)
    (ht : At t 381 ((loaderActiveFacts p l tid batch ++
      [(7168, b32 tile), (7169, b32 head), (7170, b32 batch), (7296, b64 16)]) ++ G))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop i) none) :
    ∃ u,
      X.get (g, i) = some ⟨381, .rd {loc := globalLoc (p.cuQBase + 4 * batch), size := 4}
        ((b32 (p.qOffset batch)).toBytes.map some)⟩ ∧
      X.get (g, i + 1) = some ⟨382, .rd {loc := globalLoc (p.cuQBase + 4 * (batch + 1)), size := 4}
        ((b32 (p.qOffset (batch + 1))).toBytes.map some)⟩ ∧
      X.get (g, i + 1 + 1) = some ⟨385, .rd {loc := globalLoc (p.usedKBase + 4 * batch), size := 4}
        ((b32 (p.kLength batch)).toBytes.map some)⟩ ∧
      At u 386 ([(1086, b32 (p.kLength batch)), (1799, b32 (p.qOffset batch)),
        (1800, b32 (p.qOffset (batch + 1))), (1085, b32 ((2 ^ 32 - p.qLength batch) % 2 ^ 32))] ++
        ((loaderActiveFacts p l tid batch ++
          [(7168, b32 tile), (7169, b32 head), (7170, b32 batch), (7296, b64 16)]) ++ G)) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (i + 1 + 1 + 1)) none := by
  exact loaderActiveReadWordsFrameInPrefix hp hX writes hb hG ht hr (.inl rfl)

/-- The active loader reads the two adjacent cuQ offsets and the selected request's used-K
length from their immutable global regions. The events are consecutive in the actual trace. -/
theorem loaderActiveReadWords
    (ht : At t 381 (loaderActiveFacts p l tid batch ++
      [(7168, b32 tile), (7169, b32 head), (7170, b32 batch), (7296, b64 16)]))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop i) none) :
    ∃ u,
      X.get (g, i) = some ⟨381, .rd {loc := globalLoc (p.cuQBase + 4 * batch), size := 4}
        ((b32 (p.qOffset batch)).toBytes.map some)⟩ ∧
      X.get (g, i + 1) = some ⟨382, .rd {loc := globalLoc (p.cuQBase + 4 * (batch + 1)), size := 4}
        ((b32 (p.qOffset (batch + 1))).toBytes.map some)⟩ ∧
      X.get (g, i + 1 + 1) = some ⟨385, .rd {loc := globalLoc (p.usedKBase + 4 * batch), size := 4}
        ((b32 (p.kLength batch)).toBytes.map some)⟩ ∧
      At u 386 ([(1086, b32 (p.kLength batch)), (1799, b32 (p.qOffset batch)),
        (1800, b32 (p.qOffset (batch + 1)))] ++ loaderActiveFacts p l tid batch ++
        [(7168, b32 tile), (7169, b32 head), (7170, b32 batch), (7296, b64 16)]) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (i + 1 + 1 + 1)) none := by
  obtain ⟨u, he, he', he'', hU, hTail⟩ :=
    loaderActiveReadWordsFrame hp hX writes hb (G := [])
      ⟨by simp, by simp, by simp, by set_option maxRecDepth 100000 in kernel_rfl⟩ ht hr
  exact ⟨u, he, he', he'', hU.mono ⟨hU.2.2.2.2.1, hU.2.2.2.2.2.1,
    hU.2.2.2.2.2.2.1, hU.2.2.2.2.2.2.2.2⟩, hTail⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
