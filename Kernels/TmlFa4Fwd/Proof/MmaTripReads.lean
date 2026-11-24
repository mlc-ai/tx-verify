-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaModel
public import Kernels.TmlFa4Fwd.Proof.LoaderPrefixDemand
public import Kernels.TmlFa4Fwd.Flow.Code.Part033
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpAlignment
public import Lemmas.Kernel.ReadValue
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.ProtectedReadProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof

noncomputable section

structure TripReadSite where
  pc : Nat
  base : Nat
  off : Nat
  dst : Nat

def tripReadSite : Fin 3 → TripReadSite
  | 0 => ⟨2112, 7881, 0, 2538⟩
  | 1 => ⟨2113, 7881, 4, 2539⟩
  | 2 => ⟨2116, 7882, 0, 2541⟩

/-- A scalar global read with the decoded base, byte offset and destination. -/
def tripReadMem (site : TripReadSite) : MemAccess :=
  { kind := .load, space := some .global, sem := .weak, elem := .int .b 32,
    addr := ⟨.reg site.base 64, site.off⟩, dsts := [some site.dst] }

private def tripReadCodeMatches (site : Fin 3) : Bool :=
  match kernel.code[(tripReadSite site).pc]? with
  | some ⟨none, .mem access⟩ => decide (access = tripReadMem (tripReadSite site))
  | _ => false

private theorem tripReadCode (i : Fin 3) :
    kernel.code[(tripReadSite i).pc]? = some ⟨none, .mem (tripReadMem (tripReadSite i))⟩ := by
  have hAll : (List.finRange 3).all tripReadCodeMatches = true := by decide +kernel
  have h := List.all_eq_true.mp hAll i (List.mem_finRange i)
  unfold tripReadCodeMatches at h
  split at h <;> simp_all

section
variable {l : Launch}

private theorem wordReadTemplate {g addr : Nat} {t : TState} {F : List (Nat × Value)}
    (site : TripReadSite) (hc : kernel.code[site.pc]? = some ⟨none, .mem (tripReadMem site)⟩)
    (ht : At t site.pc F) (hr : (site.base, b64 addr) ∈ F) (hAddr : addr + site.off < 2 ^ 64)
    (hAlign : (addr + site.off) % 4 = 0) :
    out kernel Assumptions.all l g t = .ev (.read
      { loc := globalLoc (addr + site.off), size := 4 }
      (afterLoad t [site.dst])) := by
  have hc' : kernel.code[t.pc]? = some ⟨none, .mem (tripReadMem site)⟩ := by simpa [ht.1] using hc
  rw [out_event ht.2.2.2.1 hc' rfl rfl]
  change Out.ev (loadTmpl Assumptions.all l g t .global false 32 [site.dst]
     site.base site.off) = _
  have hReg := holds_mem ht.2.2.2.2 hr
  have ha : addr < 2 ^ 64 := by omega
  have hEff : effAddr l g t .global site.base site.off =
      .ok (globalLoc (addr + site.off)) := by
    simp only [effAddr, readBits, readReg, hReg, b64, bind, Except.bind, pure, Except.pure,
      truncBits_ofNat ha (by decide), BitVec.ofInt_natCast, ← BitVec.ofNat_add,
      toNat_ofNat_lt hAddr]
    rfl
  simp only [loadTmpl, hEff, bind, Except.bind, List.length_singleton, ht.2.1]
  rw [elemAcc_ok (show 0 < 32 / 8 by decide) (by simpa [globalLoc] using hAlign)]
  simp [Loc.at]

/-- A decoded scalar global load observes a protected launch word at its actual event index. -/
theorem wordReadTraceNonempty {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g pos addr word : Nat} {t : TState}
    {result : Option TState} {F : List (Nat × Value)} (site : TripReadSite)
    (hc : kernel.code[site.pc]? = some ⟨none, .mem (tripReadMem site)⟩) (ht : At t site.pc F)
    (hr : (site.base, b64 addr) ∈ F) (hAddr : addr + site.off < 2 ^ 64)
    (hAlign : (addr + site.off) % 4 = 0)
    (hValue : HasValue m (globalLoc (addr + site.off)) (b32 word))
    (hProtected : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (addr + site.off)).at k)) (hFresh : ∀ pair ∈ F, pair.1 ≠ site.dst)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop pos) result)
    (hNonempty : (X.tr g).drop pos ≠ []) :
    let a : Acc := { loc := globalLoc (addr + site.off), size := 4 }
    let u := next (setReg t site.dst (b32 word))
    X.get (g, pos) = some ⟨site.pc, .rd a ((b32 word).toBytes.map some)⟩ ∧
      At u (site.pc + 1) ((site.dst, b32 word) :: F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 1)) result := by
  dsimp only
  let a : Acc := { loc := globalLoc (addr + site.off), size := 4 }
  let v := b32 word
  let hn : Next kernel Assumptions.all l g t t (.read a (afterLoad t [site.dst])) :=
    ⟨.refl, wordReadTemplate (l := l) (g := g) site hc ht hr hAddr hAlign⟩
  obtain ⟨e, u, he, hf, hNext⟩ := hn.continuing_at_nonempty (by
    rintro e ⟨bytes, _, _, hNone⟩
    cases hNone) hRun hNonempty
  obtain ⟨bytes, _, rfl, hEq⟩ := hf
  obtain rfl := Option.some.inj hEq
  have hEvent : X.get (g, pos) = some ⟨site.pc, .rd a bytes⟩ := by
    simpa only [ht.1] using he
  have hRead : X.MemReads (.thread (g, pos)) a bytes := .inl ⟨site.pc, hEvent⟩
  have hBytes : bytes = v.toBytes.map some := hX.launch_value hRead rfl hProtected hValue
  subst bytes
  have hRebuild := rebuild_scalar (v := v) (by decide : 0 < 4) rfl
  rw [afterLoad_ok ht.2.1 ht.2.2.1 hRebuild] at hNext
  have hState : { setReg t site.dst v with pc := t.pc + 1, sub := 0, acc := [] } =
      next (setReg t site.dst v) := by
    simp [next, setReg, ht.2.1, ht.2.2.1]
  rw [hState] at hNext
  exact ⟨hEvent, ht.set hFresh, hNext⟩

/-- Execute a protected word read on a terminated trace. -/
theorem wordReadTrace {m : Mem0} {X : Execution} (hX : Consistent l kernel Assumptions.all m X)
    {g pos addr word : Nat} {t : TState} {F : List (Nat × Value)} (site : TripReadSite)
    (hc : kernel.code[site.pc]? = some ⟨none, .mem (tripReadMem site)⟩) (ht : At t site.pc F)
    (hr : (site.base, b64 addr) ∈ F) (hAddr : addr + site.off < 2 ^ 64)
    (hAlign : (addr + site.off) % 4 = 0)
    (hValue : HasValue m (globalLoc (addr + site.off)) (b32 word))
    (hProtected : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (addr + site.off)).at k)) (hFresh : ∀ pair ∈ F, pair.1 ≠ site.dst)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    let a : Acc := { loc := globalLoc (addr + site.off), size := 4 }
    let u := next (setReg t site.dst (b32 word))
    X.get (g, pos) = some ⟨site.pc, .rd a ((b32 word).toBytes.map some)⟩ ∧
      At u (site.pc + 1) ((site.dst, b32 word) :: F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 1)) none :=
  wordReadTraceNonempty hX site hc ht hr hAddr hAlign hValue hProtected hFresh hRun
    (fun h => by rw [h] at hRun; cases hRun)

/-- Execute one trip-count load using the launch value of a protected input word. -/
theorem tripReadTrace {m : Mem0} {X : Execution} (hX : Consistent l kernel Assumptions.all m X)
    {g pos addr word : Nat} {t : TState} {F : List (Nat × Value)} (i : Fin 3)
    (ht : At t (tripReadSite i).pc F) (hr : ((tripReadSite i).base, b64 addr) ∈ F)
    (hAddr : addr + (tripReadSite i).off < 2 ^ 64) (hAlign : (addr + (tripReadSite i).off) % 4 = 0)
    (hValue : HasValue m (globalLoc (addr + (tripReadSite i).off)) (b32 word))
    (hProtected : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (addr + (tripReadSite i).off)).at k))
    (hFresh : ∀ pair ∈ F, pair.1 ≠ (tripReadSite i).dst)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    let a : Acc := { loc := globalLoc (addr + (tripReadSite i).off), size := 4 }
    let u := next (setReg t (tripReadSite i).dst (b32 word))
    X.get (g, pos) = some ⟨(tripReadSite i).pc, .rd a ((b32 word).toBytes.map some)⟩ ∧
      At u ((tripReadSite i).pc + 1) (((tripReadSite i).dst, b32 word) :: F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 1)) none :=
  wordReadTrace hX (tripReadSite i) (tripReadCode i) ht hr hAddr hAlign hValue
    hProtected hFresh hRun

private theorem tripReadTraceNonempty {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g pos addr word : Nat} {t : TState}
    {ending : Option TState} {F : List (Nat × Value)} (i : Fin 3) (ht : At t (tripReadSite i).pc F)
    (hr : ((tripReadSite i).base, b64 addr) ∈ F) (hAddr : addr + (tripReadSite i).off < 2 ^ 64)
    (hAlign : (addr + (tripReadSite i).off) % 4 = 0)
    (hValue : HasValue m (globalLoc (addr + (tripReadSite i).off)) (b32 word))
    (hProtected : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (addr + (tripReadSite i).off)).at k))
    (hFresh : ∀ pair ∈ F, pair.1 ≠ (tripReadSite i).dst)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop pos) ending)
    (hMore : (X.tr g).drop pos ≠ []) :
    let a : Acc := { loc := globalLoc (addr + (tripReadSite i).off), size := 4 }
    let u := next (setReg t (tripReadSite i).dst (b32 word))
    X.get (g, pos) = some ⟨(tripReadSite i).pc, .rd a ((b32 word).toBytes.map some)⟩ ∧
      At u ((tripReadSite i).pc + 1) (((tripReadSite i).dst, b32 word) :: F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 1)) ending :=
  wordReadTraceNonempty hX (tripReadSite i) (tripReadCode i) ht hr hAddr hAlign hValue
    hProtected hFresh hRun hMore

/-- Selected request register facts at the first trip-count read. -/
def tripReadEntry (p : Params) (l : Launch) (batch tile : Nat) : List (Nat × Value) :=
  [(7881, b64 (p.cuQBase + 4 * batch)), (7880, b64 (4 * batch)), (7503, b64 p.usedKBase),
    (7202, b32 (256 * (tile + 1))), (2535, b32 l.sharedBase)]

/-- Facts needed to reduce the MMA trip count after loading the selected request. -/
def tripCountEntry (p : Params) (l : Launch) (batch tile : Nat) : List (Nat × Value) :=
  [(2541, b32 (p.kLength batch)), (2540, b32 (2^32 - p.qLength batch)),
    (7202, b32 (256 * (tile + 1))), (2535, b32 l.sharedBase)]

private theorem usedKPointer {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {batch tile : Nat} (hb : batch < p.batch) (hq : 0 < p.qLength batch) :
    Seg kernel [] l g 2 2114
      ((2539, b32 (p.qOffset (batch + 1))) :: (2538, b32 (p.qOffset batch)) ::
        tripReadEntry p l batch tile) 2116
      ((7882, b64 (p.usedKBase + 4 * batch)) :: (2540, b32 (2^32 - p.qLength batch)) ::
        (7202, b32 (256 * (tile + 1))) :: [(2535, b32 l.sharedBase)]) := by
  have hA := hp.qOffset_le_total (b := batch) hb.le
  have hB := hp.qOffset_le_total (b := batch + 1) (by omega)
  have hAB := (hp.lengths batch hb).1
  have hT := hp.shape.2.2.2.2
  have hRange := hp.ranges ⟨p.usedKBase, 4 * p.batch⟩ (by simp [Params.inputRegions])
  change p.usedKBase + 4 * p.batch ≤ 2 ^ 64 at hRange
  change 0 < p.qOffset (batch + 1) - p.qOffset batch at hq
  intro t ht
  unfold tripReadEntry at ht
  seg_fp ht using norm_bits [Params.qLength]

/-- The selected request reads cuQ endpoints and used-K once, then continues at the first divide. -/
theorem tripReadsTraceInPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g pos batch tile : Nat} (hb : batch < p.batch) (hq : 0 < p.qLength batch)
    {t : TState} {ending : Option TState} (ht : At t 2112 (tripReadEntry p l batch tile))
    (hCuQ : ∀ lane ≤ 1, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * (batch + lane))).at k))
    (hUsedK : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4 * batch)).at k))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) ending)
    (hDemand : Loader.PrefixDemand X g pos 2116 ending) :
    ∃ u, At u 2117 (tripCountEntry p l batch tile) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 3)) ending ∧
      X.get (g, pos) = some ⟨2112, .rd {loc := globalLoc (p.cuQBase + 4 * batch), size := 4}
        ((b32 (p.qOffset batch)).toBytes.map some)⟩ ∧
      X.get (g, pos + 1) = some ⟨2113,
        .rd {loc := globalLoc (p.cuQBase + 4 * (batch + 1)), size := 4}
          ((b32 (p.qOffset (batch + 1))).toBytes.map some)⟩ ∧
      X.get (g, pos + 2) = some ⟨2116, .rd {loc := globalLoc (p.usedKBase + 4 * batch), size := 4}
        ((b32 (p.kLength batch)).toBytes.map some)⟩ := by
  have hQ := hp.alignment.2.2.2.2.2.2.2.2.1
  have hK := hp.alignment.2.2.2.2.2.2.2.2.2.1
  have hCuRange := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  have hKRange := hp.ranges ⟨p.usedKBase, 4 * p.batch⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hCuRange
  change p.usedKBase + 4 * p.batch ≤ 2 ^ 64 at hKRange
  let a := p.cuQBase + 4 * batch
  have hQ0 : a + (tripReadSite 0).off = a := rfl
  have hQ1 : a + (tripReadSite 1).off = p.cuQBase + 4 * (batch + 1) := by
    dsimp only [a, tripReadSite]
    omega
  obtain ⟨he₀, hv, hV⟩ := tripReadTraceNonempty hX (addr := a) (word := p.qOffset batch) 0 ht
    (by simp [tripReadSite, tripReadEntry, a]) (by rw [hQ0]; dsimp only [a]; omega)
    (by rw [hQ0]; dsimp only [a]; omega) (by rw [hQ0]; exact hp.cuQ _ hb.le)
    (by rw [hQ0]; simpa only [Nat.add_zero] using hCuQ 0 (by decide))
    (by
      intro pair hPair
      simp only [tripReadEntry, List.mem_cons, List.not_mem_nil, or_false] at hPair
      rcases hPair with rfl | rfl | rfl | rfl | rfl <;> exact of_decide_eq_true rfl) hr
    (hDemand.nonempty hr)
  have hSecond := hDemand.advance he₀ (by decide : (tripReadSite 0).pc ≤ 2116)
  obtain ⟨he₁, hw, hW⟩ := tripReadTraceNonempty hX (addr := a) (word := p.qOffset (batch + 1)) 1 hv
    (by simp [tripReadSite, tripReadEntry, a]) (by rw [hQ1]; omega)
    (by rw [hQ1]; omega) (by rw [hQ1]; exact hp.cuQ _ (by omega))
    (by rw [hQ1]; exact hCuQ 1 (by decide))
    (by
      intro pair hPair
      simp only [tripReadEntry, tripReadSite, List.mem_cons, List.not_mem_nil, or_false] at hPair
      rcases hPair with rfl | rfl | rfl | rfl | rfl | rfl <;> exact of_decide_eq_true rfl) hV
    (hSecond.nonempty hV)
  have hThird := hSecond.advance he₁ (by decide : (tripReadSite 1).pc ≤ 2116)
  obtain ⟨b, hLocal, hAt⟩ := usedKPointer hp g hb hq _ hw
  have hPc : (next (setReg (next (setReg t 2538 (b32 (p.qOffset batch)))) 2539
      (b32 (p.qOffset (batch + 1))))).pc = 2114 := hw.1
  have hLocalA := localRun (by decide) (by decide) hPc (by
    set_option maxRecDepth 100000 in kernel_rfl) hLocal
  obtain ⟨he₂, hu, hU⟩ := tripReadTraceNonempty hX (addr := p.usedKBase + 4 * batch)
    (word := p.kLength batch) 2 hAt (by simp [tripReadSite])
    (by simp only [tripReadSite, Nat.add_zero]; omega)
    (by simp only [tripReadSite, Nat.add_zero]; omega)
    (hp.usedK _ hb) hUsedK
    (by
      intro pair hPair
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hPair
      rcases hPair with rfl | rfl | rfl | rfl <;> exact of_decide_eq_true rfl)
    (hW.after_local_nonempty (run_rtg hLocalA) (hThird.nonempty hW)) (hThird.nonempty hW)
  refine ⟨_, hu.mono ⟨hu.2.2.2.2.1, hu.2.2.2.2.2.2⟩, ?_, he₀, ?_, ?_⟩
  · simpa only [Nat.add_assoc] using hU
  · rw [← hQ1]
    exact he₁
  · simpa only [tripReadSite, Nat.add_zero, Nat.add_assoc] using he₂

/-- A protected global scalar load occurs at a reached decoded cursor in a maximal trace. -/
theorem wordReadOfMaximal {m : Mem0} {X : Execution} (hMax : Maximal l kernel Assumptions.all m X)
    {g pos addr word : Nat} (hg : g < l.threads) (site : TripReadSite)
    (hc : kernel.code[site.pc]? = some ⟨none, .mem (tripReadMem site)⟩) {s t : TState}
    {F : List (Nat × Value)} {ending : Option TState} (ht : At t site.pc F)
    (hr : (site.base, b64 addr) ∈ F) (hAddr : addr + site.off < 2 ^ 64)
    (hAlign : (addr + site.off) % 4 = 0)
    (hValue : HasValue m (globalLoc (addr + site.off)) (b32 word))
    (hProtected : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (addr + site.off)).at k)) (hFresh : ∀ pair ∈ F, pair.1 ≠ site.dst)
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some s))
    (hRun : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending)
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t) (hPos : 0 < pos)
    (hBound : pos ≤ (X.tr g).length) (hRelease : pos = (X.tr g).length → Step.Released l X g) :
    ∃ u, X.get (g,pos) = some ⟨site.pc,
        .rd {loc := globalLoc (addr + site.off),size := 4}
          ((b32 word).toBytes.map some)⟩ ∧
      At u (site.pc + 1) ((site.dst,b32 word) :: F) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (pos+1)) (some u) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos+1)) ending := by
  have hn : Next kernel Assumptions.all l g s t (.read
      {loc := globalLoc (addr + site.off),size := 4}
      (afterLoad t [site.dst])) :=
    ⟨hLocal,wordReadTemplate site hc ht hr hAddr hAlign⟩
  obtain ⟨he,hPast,hTail⟩ := Step.protected_read_of_maximal hMax hg (value := b32 word)
    (a := {loc := globalLoc (addr + site.off),size := 4})
    rfl hValue hProtected hn hPrefix hRun hPos hBound hRelease
    (Assumptions.wf_snoc_initial hMax.1)
  have hRebuild := rebuild_scalar (v := b32 word) (show 0 < 4 by decide) rfl
  rw [afterLoad_ok ht.2.1 ht.2.2.1 hRebuild] at hPast hTail
  have hState : { setReg t site.dst (b32 word)
                    with pc := t.pc + 1, sub := 0, acc := [] } =
      next (setReg t site.dst (b32 word)) := by
    simp [next,setReg,ht.2.1,ht.2.2.1]
  rw [hState] at hPast hTail
  exact ⟨_,ht.1 ▸ he,ht.set hFresh,hPast,hTail⟩
end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g pos batch tile : Nat} (hg : g < l.threads)
    (hb : batch < p.batch) (hq : 0 < p.qLength batch) {s t : TState} {ending : Option TState}
    (ht : At t 2112 (tripReadEntry p l batch tile))
    (hCuQ : ∀ lane ≤ 1, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * (batch + lane))).at k))
    (hUsedK : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4 * batch)).at k))
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some s))
    (hRun : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending)
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t) (hPos : 0 < pos)
    (hBound : pos ≤ (X.tr g).length)
include hp hMax hg hb hq ht hCuQ hUsedK hPrefix hRun hLocal hPos hBound

/-- The selected maximal MMA trace records both CuQ endpoints and its used-K read. -/
theorem tripReadsWithEventsOfMaximal (hRelease : pos = (X.tr g).length → Step.Released l X g) :
    ∃ u, (X.get (g, pos) = some ⟨2112, .rd {loc := globalLoc (p.cuQBase + 4 * batch), size := 4}
        ((b32 (p.qOffset batch)).toBytes.map some)⟩) ∧
      (X.get (g, pos + 1) = some ⟨2113,
        .rd {loc := globalLoc (p.cuQBase + 4 * (batch + 1)), size := 4}
          ((b32 (p.qOffset (batch + 1))).toBytes.map some)⟩) ∧
      (X.get (g, pos + 2) = some ⟨2116, .rd {loc := globalLoc (p.usedKBase + 4 * batch), size := 4}
        ((b32 (p.kLength batch)).toBytes.map some)⟩) ∧
      At u 2117 (tripCountEntry p l batch tile) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (pos+3)) (some u) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos+3)) ending ∧
      pos+3 ≤ (X.tr g).length ∧ (pos+3 = (X.tr g).length → Step.Released l X g) := by
  have hQ := hp.alignment.2.2.2.2.2.2.2.2.1
  have hK := hp.alignment.2.2.2.2.2.2.2.2.2.1
  have hCuRange := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  have hKRange := hp.ranges ⟨p.usedKBase, 4 * p.batch⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hCuRange
  have hUsedRange : p.usedKBase + 4 * p.batch ≤ 2 ^ 64 := hKRange
  let a := p.cuQBase + 4 * batch
  have hQ0 : a + (tripReadSite 0).off = a := rfl
  have hQ1 : a + (tripReadSite 1).off = p.cuQBase + 4 * (batch + 1) := by
    dsimp only [a, tripReadSite]
    omega
  obtain ⟨v,he₀,hv,hPast,hV⟩ := wordReadOfMaximal hMax hg
    (addr := a) (word := p.qOffset batch) (tripReadSite 0) (tripReadCode 0) ht
    (by simp [tripReadSite, tripReadEntry, a]) (by rw [hQ0]; dsimp only [a]; omega)
    (by rw [hQ0]; dsimp only [a]; omega) (by rw [hQ0]; exact hp.cuQ _ hb.le)
    (by rw [hQ0]; simpa only [Nat.add_zero] using hCuQ 0 (by decide))
    (by
      intro pair hPair
      simp only [tripReadEntry,List.mem_cons,List.not_mem_nil,or_false] at hPair
      rcases hPair with rfl | rfl | rfl | rfl | rfl <;> exact of_decide_eq_true rfl)
    hPrefix hRun hLocal hPos hBound hRelease
  obtain ⟨w,he₁,hw,hPast',hW⟩ := wordReadOfMaximal hMax hg
    (addr := a) (word := p.qOffset (batch+1)) (tripReadSite 1) (tripReadCode 1) hv
    (by simp [tripReadSite, tripReadEntry, a]) (by rw [hQ1]; omega)
    (by rw [hQ1]; omega) (by rw [hQ1]; exact hp.cuQ _ (by omega))
    (by rw [hQ1]; exact hCuQ 1 (by decide))
    (by
      intro pair hPair
      simp only [tripReadEntry,tripReadSite,List.mem_cons,List.not_mem_nil,or_false] at hPair
      rcases hPair with rfl | rfl | rfl | rfl | rfl | rfl <;> exact of_decide_eq_true rfl)
    hPast hV .refl (Nat.succ_pos _) (len_of_get he₀)
    (Prologue.releasedIfLast he₀ (by intro h; cases h))
  obtain ⟨b,hLocalK,hAt⟩ := usedKPointer hp g hb hq w hw
  have hLocalK' := localRun (by decide) (by decide) hw.1 (by
    set_option maxRecDepth 100000 in kernel_rfl) hLocalK
  obtain ⟨u,he₂,hu,hPast'',hU⟩ := wordReadOfMaximal hMax hg
    (addr := p.usedKBase + 4 * batch) (word := p.kLength batch)
    (tripReadSite 2) (tripReadCode 2) hAt
    (by simp [tripReadSite])
    (by simp only [tripReadSite,Nat.add_zero]; omega)
    (by simp only [tripReadSite,Nat.add_zero]; omega)
    (hp.usedK _ hb) hUsedK
    (by
      intro pair hPair
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hPair
      rcases hPair with rfl | rfl | rfl | rfl <;> exact of_decide_eq_true rfl)
    hPast' hW (run_rtg hLocalK') (Nat.succ_pos _) (len_of_get he₁)
    (Prologue.releasedIfLast he₁ (by intro h; cases h))
  have hEq : pos+1+1+1 = pos+3 := by omega
  have he₀' : X.get (g,pos) = some ⟨2112, .rd {loc := globalLoc a, size := 4}
      ((b32 (p.qOffset batch)).toBytes.map some)⟩ := by
    simpa only [tripReadSite, Nat.add_zero] using he₀
  have he₁' := hQ1 ▸ he₁
  have he₂' := (show pos+1+1 = pos+2 by omega) ▸ he₂
  refine ⟨u,he₀',he₁',?_,hu.mono ⟨hu.2.2.2.2.1,hu.2.2.2.2.2.2⟩,
    hEq ▸ hPast'',hEq ▸ hU,hEq ▸ len_of_get he₂,
    hEq ▸ Prologue.releasedIfLast he₂ (by intro h; cases h)⟩
  simpa only [tripReadSite, Nat.add_zero] using he₂'

/-- The selected MMA trace continues at the trip count after reading launch metadata. -/
theorem tripReadsOfMaximal (hRelease : pos = (X.tr g).length → Step.Released l X g) :
    ∃ u, At u 2117 (tripCountEntry p l batch tile) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (pos+3)) (some u) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos+3)) ending ∧
      pos+3 ≤ (X.tr g).length ∧ (pos+3 = (X.tr g).length → Step.Released l X g) := by
  obtain ⟨u, _, _, _, hAt, hPast, hSuffix, hLen, hReleased⟩ :=
    tripReadsWithEventsOfMaximal hp hMax hg hb hq ht hCuQ hUsedK
      hPrefix hRun hLocal hPos hBound hRelease
  exact ⟨u, hAt, hPast, hSuffix, hLen, hReleased⟩

end
end PTX.Kernels.TmlFa4Fwd.Mma
