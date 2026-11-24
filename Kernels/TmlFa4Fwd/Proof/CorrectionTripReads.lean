-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionTripCount
public import Lemmas.Kernel.ReadValue
public import Lemmas.Flow.TraceReach
import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Kernels.TmlFa4Fwd.Flow.Code.Part124
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Kernels.TmlFa4Fwd.Proof.InputRead
import Lemmas.Step.DrainInOrder
import Lemmas.Step.ProtectedReadProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof PTX.EventFrame Epilogue Mma

noncomputable section

private structure TripReadSite where
  pc : Nat
  base : Nat
  off : Nat
  dst : Nat

private def tripReadSite : Fin 3 → TripReadSite
  | 0 => ⟨7955, 8992, 0, 1634⟩
  | 1 => ⟨7956, 8992, 4, 5958⟩
  | 2 => ⟨7959, 8993, 0, 5959⟩

private def tripReadMem (site : TripReadSite) : MemAccess :=
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

private theorem tripReadTemplate {l : Launch} {g addr : Nat} {t : TState}
    {F : List (Nat × Value)} (i : Fin 3)
    (ht : At t (tripReadSite i).pc F)
    (hr : ((tripReadSite i).base, b64 addr) ∈ F)
    (hAddr : addr + (tripReadSite i).off < 2 ^ 64)
    (hAlign : (addr + (tripReadSite i).off) % 4 = 0) :
    out kernel Assumptions.all l g t = .ev (.read
      { loc := globalLoc (addr + (tripReadSite i).off), size := 4 }
      (afterLoad t [(tripReadSite i).dst])) := by
  have hCode := ht.1.symm ▸ tripReadCode i
  have hModel : out kernel Assumptions.all l g t = out kernel [] l g t := by
    apply Assumptions.out_all_eq_nil _ _ _ hCode rfl
    all_goals rw [ht.1]; fin_cases i <;> decide
  rw [hModel, out_event ht.2.2.2.1 hCode rfl rfl]
  change Out.ev (loadTmpl [] l g t .global false 32 [(tripReadSite i).dst]
     (tripReadSite i).base (tripReadSite i).off) = _
  have hReg := holds_mem ht.2.2.2.2 hr
  have ha : addr < 2 ^ 64 := by omega
  have hEff : effAddr l g t .global (tripReadSite i).base (tripReadSite i).off =
      .ok (globalLoc (addr + (tripReadSite i).off)) := by
    simp only [effAddr, readBits, readReg, hReg, b64, bind, Except.bind, pure, Except.pure,
      truncBits_ofNat ha (by decide), BitVec.ofInt_natCast, ← BitVec.ofNat_add,
      toNat_ofNat_lt hAddr]
    rfl
  simp only [loadTmpl, hEff, bind, Except.bind, List.length_singleton, ht.2.1]
  rw [elemAcc_ok (show 0 < 32 / 8 by decide) (by simpa [globalLoc] using hAlign)]
  simp [Loc.at]

/-- The read sequence is required when the run ends, or when the lane has a later event. -/
def CorrectionTripSuffix (X : Execution) (g pos : Nat) (o : Option TState)
    (first : Nat := 7960) : Prop :=
  o = none ∨ ∃ j e, pos ≤ j ∧ first ≤ e.pc ∧ X.get (g, j) = some e

private theorem tripSuffixNonempty {l : Launch} {X : Execution} {g pos first : Nat} {t : TState}
    {o : Option TState} (hSuffix : CorrectionTripSuffix X g pos o first)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) o) :
    (X.tr g).drop pos ≠ [] := by
  intro he
  rcases hSuffix with h | ⟨j, e, hj, _, hE⟩
  · subst o
    rw [he] at hr
    cases hr
  · have hLen := List.drop_eq_nil_iff.mp he
    have hJ : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp hE).1
    omega

private theorem tripSuffixAdvance {X : Execution} {g pos first : Nat} {o : Option TState}
    {e : Event} (hSuffix : CorrectionTripSuffix X g pos o first)
    (hE : X.get (g, pos) = some e) (hPC : e.pc < first) :
    CorrectionTripSuffix X g (pos + 1) o first := by
  rcases hSuffix with h | ⟨j, f, hJ, hF, hf⟩
  · exact .inl h
  · have hNe : j ≠ pos := by
      intro h
      subst j
      obtain rfl := Option.some.inj (hf.symm.trans hE)
      omega
    exact .inr ⟨j, f, by omega, hF, hf⟩

/-- A protected word's reads return its launch value. -/
private theorem readsOfProtected {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {addr word : Nat}
    (hValue : HasValue m (globalLoc addr) (b32 word))
    (hProtected : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs → ¬ a.Covers ((globalLoc addr).at k)) :
    ∀ j bs, X.Reads j {loc := globalLoc addr, size := 4} bs → bs = (b32 word).toBytes.map some :=
  fun j _ h => hX.launch_value (r := .thread j) (.inl h) rfl hProtected hValue

/-- Execute one trip-count load whose reads return the launch value of an input word. -/
private theorem tripReadTrace {l : Launch} {X : Execution}
    {g pos addr word : Nat} {t : TState} {F : List (Nat × Value)} {o : Option TState}
    (i : Fin 3)
    (ht : At t (tripReadSite i).pc F)
    (hr : ((tripReadSite i).base, b64 addr) ∈ F)
    (hAddr : addr + (tripReadSite i).off < 2 ^ 64)
    (hAlign : (addr + (tripReadSite i).off) % 4 = 0)
    (hWord : ∀ j bs, X.Reads j {loc := globalLoc (addr + (tripReadSite i).off), size := 4} bs →
      bs = (b32 word).toBytes.map some)
    (hFresh : ∀ pair ∈ F, pair.1 ≠ (tripReadSite i).dst)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop pos) o)
    (hMore : (X.tr g).drop pos ≠ []) :
    let a : Acc := { loc := globalLoc (addr + (tripReadSite i).off), size := 4 }
    let u := next (setReg t (tripReadSite i).dst (b32 word))
    X.get (g, pos) = some ⟨(tripReadSite i).pc, .rd a ((b32 word).toBytes.map some)⟩ ∧
      At u ((tripReadSite i).pc + 1) (((tripReadSite i).dst, b32 word) :: F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 1)) o ∧
      EStep kernel Assumptions.all l g t
        ⟨(tripReadSite i).pc, .rd a ((b32 word).toBytes.map some)⟩ (some u) := by
  dsimp only
  let site := tripReadSite i
  let a : Acc := { loc := globalLoc (addr + site.off), size := 4 }
  let v := b32 word
  let hn : Next kernel Assumptions.all l g t t (.read a (afterLoad t [site.dst])) :=
    ⟨.refl, tripReadTemplate (l := l) (g := g) i ht hr hAddr hAlign⟩
  obtain ⟨e, u, he, hf, hNext⟩ := hn.continuing_at_nonempty (by
    rintro e ⟨bytes, _, _, hNone⟩
    cases hNone) hRun hMore
  have hStep : EStep kernel Assumptions.all l g t e (some u) := ⟨_, hn.stop, hf⟩
  obtain ⟨bytes, _, rfl, hEq⟩ := hf
  obtain rfl := Option.some.inj hEq
  have hEvent : X.get (g, pos) = some ⟨site.pc, .rd a bytes⟩ := by
    simpa only [ht.1] using he
  have hBytes : bytes = v.toBytes.map some := hWord _ _ ⟨site.pc, hEvent⟩
  subst bytes
  have hRebuild := rebuild_scalar (v := v) (by decide : 0 < 4) rfl
  rw [afterLoad_ok ht.2.1 ht.2.2.1 hRebuild] at hNext hStep
  have hState : { setReg t site.dst v with pc := t.pc + 1, sub := 0, acc := [] } =
      next (setReg t site.dst v) := by
    simp [next, setReg, ht.2.1, ht.2.2.1]
  rw [hState] at hNext hStep
  exact ⟨hEvent, ht.set hFresh, hNext,
    by simpa only [ht.1] using hStep⟩

/-- A returning lane cursor tied to the actual trace boundary of a protected correction read. -/
structure OpeningTripCursor (l : Launch) (X : Execution) (g pc : Nat)
    (F : List (Nat × Value)) where
  pos : Nat
  before : TState
  ready : TState
  ending : Option TState
  positive : 0 < pos
  bounded : pos ≤ (X.tr g).length
  released : pos = (X.tr g).length → Step.Released l X g
  checkpoint : At ready pc F
  recorded : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some before)
  remaining : Run kernel Assumptions.all l g before ((X.tr g).drop pos) ending
  localSteps : Relation.ReflTransGen (Tau kernel Assumptions.all l g) before ready

private theorem tripReadOfMaximal {l : Launch} {m : Mem0} {X : Execution}
    (hMax : Maximal l kernel Assumptions.all m X) {g addr word : Nat} (hg : g < l.threads)
    (i : Fin 3) {F : List (Nat × Value)} (c : OpeningTripCursor l X g (tripReadSite i).pc F)
    (hr : ((tripReadSite i).base,b64 addr) ∈ F)
    (hAddr : addr+(tripReadSite i).off < 2^64) (hAlign : (addr+(tripReadSite i).off)%4 = 0)
    (hValue : HasValue m (globalLoc (addr+(tripReadSite i).off)) (b32 word))
    (hProtected : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (addr+(tripReadSite i).off)).at k))
    (hFresh : ∀ pair ∈ F, pair.1 ≠ (tripReadSite i).dst) :
    Nonempty (OpeningTripCursor l X g ((tripReadSite i).pc+1)
      (((tripReadSite i).dst,b32 word) :: F)) := by
  let site := tripReadSite i
  let a : Acc := {loc := globalLoc (addr+site.off),size := 4}
  let bytes := (b32 word).toBytes.map some
  let u := next (setReg c.ready site.dst (b32 word))
  let hn : Next kernel Assumptions.all l g c.before c.ready
      (.read a (afterLoad c.ready [site.dst])) :=
    ⟨c.localSteps,tripReadTemplate i c.checkpoint hr hAddr hAlign⟩
  obtain ⟨he,hPrefix,hTail⟩ := Step.protected_read_of_maximal hMax hg
    (a := a) (value := b32 word) rfl hValue hProtected hn c.recorded c.remaining c.positive
    c.bounded c.released (Assumptions.wf_snoc_initial hMax.1)
  have hRebuild := rebuild_scalar (v := b32 word) (by decide : 0 < 4) rfl
  have hState : afterLoad c.ready [site.dst] bytes = u := by
    rw [afterLoad_ok c.checkpoint.2.1 c.checkpoint.2.2.1 hRebuild]
    simp [u,next,setReg,c.checkpoint.2.1,c.checkpoint.2.2.1]
  rw [hState] at hPrefix hTail
  refine ⟨⟨c.pos+1,u,u,c.ending,Nat.succ_pos _,len_of_get he,?_,c.checkpoint.set hFresh,
    hPrefix,hTail,.refl⟩⟩
  intro hLast
  apply Step.Released.of_get
  intro e hGet
  have hPrev : (X.tr g).length-1 = c.pos := by omega
  rw [hPrev,he] at hGet
  cases hGet
  simp [Kind.resume]

/-- The first read uses the selected request's cumulative-query pointer. -/
def correctionInputFacts (p : Params) (batch tile : Nat) : List (Nat × Value) :=
  [(8992, b64 (p.cuQBase + 4 * batch)), (8991, b64 (4 * batch)), (7503, b64 p.usedKBase),
    (7276, b32 tile)]

private theorem usedKPointer {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) {batch tile : Nat} (hb : batch < p.batch) :
    Seg kernel [] l g 2 7957
      ((5958, b32 (p.qOffset (batch + 1))) :: (1634, b32 (p.qOffset batch)) ::
        correctionInputFacts p batch tile) 7959
      [(8993, b64 (p.usedKBase + 4 * batch)), (1635, b32 (p.qLength batch)),
        (7276, b32 tile), (1634, b32 (p.qOffset batch))] := by
  have hA := hp.qOffset_le_total (b := batch) hb.le
  have hB := hp.qOffset_le_total (b := batch + 1) (by omega)
  have hAB := (hp.lengths batch hb).1
  have hT := hp.shape.2.2.2.2
  have hRange := hp.ranges ⟨p.usedKBase, 4 * p.batch⟩ (by simp [Params.inputRegions])
  change p.usedKBase + 4 * p.batch ≤ 2 ^ 64 at hRange
  intro t ht
  unfold correctionInputFacts at ht
  seg_fp ht using norm_bits [Params.qLength]

private theorem afterFirstWords {l : Launch} {g : Nat} {t u : TState}
    (hPc : t.pc = 7957) (hLocal : run kernel [] l g 2 t = some u) :
    run kernel Assumptions.all l g 2 t = some u := by
  apply schedulerLocalTransport (lo := 7957) (len := 2) (by
    set_option maxRecDepth 100000 in kernel_rfl) _ hLocal hPc.ge (by rw [hPc])
  intro s hlo hhi
  have hn : s.pc = 7957 ∨ s.pc = 7958 := by omega
  rcases hn with hn | hn
  · apply Assumptions.out_all_eq_nil _ _ _ (hn.symm ▸ Flow.code_7957) rfl
    all_goals rw [hn]; decide
  · apply Assumptions.out_all_eq_nil _ _ _ (hn.symm ▸ Flow.code_7958) rfl
    all_goals rw [hn]; decide

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g pos batch tile : Nat} (hb : batch < p.batch)
include hp hX hb

/-- Read the selected request's first cumulative-query word, including at a prefix end. -/
theorem correctionFirstCuQInPrefix {t : TState} {F : List (Nat × Value)} {o : Option TState}
    (ht : At t 7955 (correctionInputFacts p batch tile ++ F)) (hFresh : ∀ rv ∈ F, rv.1 ≠ 1634)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) o) (hMore : (X.tr g).drop pos ≠ []) :
    let e : Event := ⟨7955, .rd {loc := globalLoc (p.cuQBase + 4 * batch), size := 4}
      ((b32 (p.qOffset batch)).toBytes.map some)⟩
    let u := next (setReg t 1634 (b32 (p.qOffset batch)))
    X.get (g, pos) = some e ∧
      At u 7956 ((1634, b32 (p.qOffset batch)) :: correctionInputFacts p batch tile ++ F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 1)) o ∧
      EStep kernel Assumptions.all l g t e (some u) := by
  dsimp only
  have hQ := hp.alignment.2.2.2.2.2.2.2.2.1
  have hCuRange := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hCuRange
  let a := p.cuQBase + 4 * batch
  have hQ0 : a + (tripReadSite 0).off = a := rfl
  obtain ⟨he₀, hv, hV, hStep0⟩ :=
    tripReadTrace (addr := a) (word := p.qOffset batch) 0 ht
    (by simp [tripReadSite, correctionInputFacts, a]) (by rw [hQ0]; dsimp only [a]; omega)
    (by rw [hQ0]; dsimp only [a]; omega) (by rw [hQ0]; exact cuQWordReads hp hX hb.le)
    (by
      intro pair hPair
      rcases List.mem_append.mp hPair with hBase | hFrame
      · simp only [correctionInputFacts, List.mem_cons, List.not_mem_nil, or_false] at hBase
        rcases hBase with rfl | rfl | rfl | rfl <;> exact of_decide_eq_true rfl
      · intro he
        exact hFresh pair hFrame (by simpa [tripReadSite] using he)) hr hMore
  exact ⟨he₀, hv, hV, hStep0⟩

/-- Read the selected request's second cumulative-query word, including at a prefix end. -/
theorem correctionSecondCuQInPrefix {t : TState} {F : List (Nat × Value)} {o : Option TState}
    (hv : At t 7956 ((1634, b32 (p.qOffset batch)) :: correctionInputFacts p batch tile ++ F))
    (hFresh : ∀ rv ∈ F, rv.1 ≠ 5958) (hV : Run kernel Assumptions.all l g t ((X.tr g).drop pos) o)
    (hMore : (X.tr g).drop pos ≠ []) :
    let e : Event := ⟨7956, .rd {loc := globalLoc (p.cuQBase + 4 * (batch + 1)), size := 4}
      ((b32 (p.qOffset (batch + 1))).toBytes.map some)⟩
    let u := next (setReg t 5958 (b32 (p.qOffset (batch + 1))))
    X.get (g, pos) = some e ∧
      At u 7957 ((5958, b32 (p.qOffset (batch + 1))) :: (1634, b32 (p.qOffset batch)) ::
        correctionInputFacts p batch tile ++ F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 1)) o ∧
      EStep kernel Assumptions.all l g t e (some u) := by
  dsimp only
  have hQ := hp.alignment.2.2.2.2.2.2.2.2.1
  have hCuRange := hp.ranges ⟨p.cuQBase, 4 * (p.batch + 1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase + 4 * (p.batch + 1) ≤ 2 ^ 64 at hCuRange
  let a := p.cuQBase + 4 * batch
  have hQ1 : a + (tripReadSite 1).off = p.cuQBase + 4 * (batch + 1) := by
    dsimp only [a, tripReadSite]
    omega
  obtain ⟨he₁, hw, hW, hStep1⟩ := tripReadTrace (addr := a)
    (word := p.qOffset (batch + 1)) 1 hv
    (by simp [tripReadSite, correctionInputFacts, a]) (by rw [hQ1]; omega)
    (by rw [hQ1]; omega) (by rw [hQ1]; exact cuQWordReads hp hX (by omega))
    (by
      intro pair hPair
      rcases List.mem_cons.mp hPair with rfl | hPair
      · exact of_decide_eq_true rfl
      · rcases List.mem_append.mp hPair with hBase | hFrame
        · simp only [correctionInputFacts, List.mem_cons, List.not_mem_nil, or_false] at hBase
          rcases hBase with rfl | rfl | rfl | rfl <;> exact of_decide_eq_true rfl
        · intro he
          exact hFresh pair hFrame (by simpa [tripReadSite] using he)) hV
    hMore
  exact ⟨he₁, hw, hW, hStep1⟩

omit hp hX hb in
/-- Record the actual CuQ endpoint reads and carry their decoded geometry to the UsedK load. -/
theorem correctionCuQReadsToUsedKInPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g pos batch tile : Nat} {first : Nat} (hb : batch < p.batch)
    {t : TState} {F : List (Nat × Value)} {o : Option TState}
    (ht : At t 7955 (correctionInputFacts p batch tile ++ F))
    (hFresh : ∀ rv ∈ F, rv.1 ∉ [1634, 5958, 5959])
    (hWrites : ((kernel.code.drop 7957).take 2).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) o)
    (hSuffix : CorrectionTripSuffix X g pos o first) (hFirst : 7956 < first) :
    ∃ u, At u 7959
        ([(8993, b64 (p.usedKBase + 4 * batch)), (1635, b32 (p.qLength batch)),
          (7276, b32 tile), (1634, b32 (p.qOffset batch))] ++ F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 2)) o ∧
      X.get (g, pos) = some ⟨7955, .rd {loc := globalLoc (p.cuQBase + 4 * batch), size := 4}
        ((b32 (p.qOffset batch)).toBytes.map some)⟩ ∧
      X.get (g, pos + 1) = some ⟨7956,
        .rd {loc := globalLoc (p.cuQBase + 4 * (batch + 1)), size := 4}
          ((b32 (p.qOffset (batch + 1))).toBytes.map some)⟩ ∧
      CorrectionTripSuffix X g (pos + 2) o first ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop pos).take 2) u := by
  obtain ⟨he₀, hv, hV, hStep0⟩ := correctionFirstCuQInPrefix hp hX hb ht
    (fun rv h => fun eq => hFresh rv h (by simp [eq])) hr (tripSuffixNonempty hSuffix hr)
  have hvSuffix := tripSuffixAdvance hSuffix he₀ (show 7955 < first by omega)
  obtain ⟨he₁, hw, hW, hStep1⟩ := correctionSecondCuQInPrefix hp hX hb hv
    (fun rv h => fun eq => hFresh rv h (by simp [eq])) hV
    (tripSuffixNonempty hvSuffix hV)
  have hwSuffix := tripSuffixAdvance hvSuffix he₁ hFirst
  have hOld := (holds_append _ _ _).1 hw.2.2.2.2.2.2
  obtain ⟨b, hLocal, hAt⟩ := usedKPointer hp g hb _
    (hw.mono ⟨hw.2.2.2.2.1, hw.2.2.2.2.2.1, hOld.1⟩)
  have hCore := afterFirstWords hw.1 hLocal
  have hFrame : ∀ r ∈ F.map Prod.fst, b.regs r =
      (next (setReg (next (setReg t 1634 (b32 (p.qOffset batch)))) 5958
        (b32 (p.qOffset (batch + 1))))).regs r :=
    fun _ hm => schedulerLocalFrame (lo := 7957) (len := 2) hWrites
      (by set_option maxRecDepth 100000 in kernel_rfl) hLocal hw.1.ge
      (by rw [hw.1]) hm
  have hSaved := holdsSchedulerFrame hOld.2 hFrame (fun _ hm => List.mem_map_of_mem hm)
  have hAt' : At b 7959
      ([(8993, b64 (p.usedKBase + 4 * batch)), (1635, b32 (p.qLength batch)),
        (7276, b32 tile), (1634, b32 (p.qOffset batch))] ++ F) :=
    hAt.mono ((holds_append _ _ _).2 ⟨hAt.2.2.2.2, hSaved⟩)
  have hTail := hW.after_local_nonempty (run_rtg hCore) (tripSuffixNonempty hwSuffix hW)

  have hEq : ((X.tr g).drop pos).take 2 =
      [⟨7955, .rd {loc := globalLoc (p.cuQBase + 4 * batch), size := 4}
          ((b32 (p.qOffset batch)).toBytes.map some)⟩,
        ⟨7956, .rd {loc := globalLoc (p.cuQBase + 4 * (batch + 1)), size := 4}
          ((b32 (p.qOffset (batch + 1))).toBytes.map some)⟩] := by
    apply List.ext_getElem?
    intro i
    rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | hi
    · rw [List.getElem?_take_of_lt (by decide), List.getElem?_drop]
      exact he₀
    · rw [List.getElem?_take_of_lt (by decide), List.getElem?_drop]
      exact he₁
    · rw [List.getElem?_eq_none (by rw [List.length_take]; omega),
        List.getElem?_eq_none (by simpa using hi)]
  have hReach : TraceReach kernel Assumptions.all l g t (((X.tr g).drop pos).take 2) b := by
    rw [hEq]
    exact .event hStep0 (.event hStep1 (TraceReach.of_local (run_rtg hCore)))
  exact ⟨b, hAt', hTail, he₀, he₁, hwSuffix, hReach⟩

omit hp hX hb in
private theorem faultWalkPc {l : Launch} {g : Nat} {t : TState} {f : Fault}
    {events : List Event} {visits : List Visit} {target : Event}
    (hf : t.fault = some f) (hw : Walk kernel Assumptions.all l g t events visits)
    (hTarget : target ∈ events) : target.pc = t.pc := by
  cases hw with
  | stop => simp at hTarget
  | tau h _ => simp [Tau, out, hf] at h
  | ev h _ =>
    obtain ⟨templ, ho, hFire⟩ := h
    simp only [out, hf, Out.ev.injEq] at ho
    subst templ
    have hBad : some _ = none := hFire.2
    cases hBad
  | last h =>
    obtain rfl := List.mem_singleton.mp hTarget
    exact estep_source_pc h

/-- Recover the CuQ reads when replay continues beyond the UsedK load. -/
theorem correctionCuQReadsToUsedK {t : TState} {F : List (Nat × Value)} {o : Option TState}
    (ht : At t 7955 (correctionInputFacts p batch tile ++ F))
    (hFresh : ∀ rv ∈ F, rv.1 ∉ [1634, 5958, 5959])
    (hWrites : ((kernel.code.drop 7957).take 2).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) o)
    (hSuffix : CorrectionTripSuffix X g pos o) :
    ∃ u, At u 7959
        ([(8993, b64 (p.usedKBase + 4 * batch)), (1635, b32 (p.qLength batch)),
          (7276, b32 tile), (1634, b32 (p.qOffset batch))] ++ F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 2)) o ∧
      X.get (g, pos) = some ⟨7955, .rd {loc := globalLoc (p.cuQBase + 4 * batch), size := 4}
        ((b32 (p.qOffset batch)).toBytes.map some)⟩ ∧
      X.get (g, pos + 1) = some ⟨7956,
        .rd {loc := globalLoc (p.cuQBase + 4 * (batch + 1)), size := 4}
          ((b32 (p.qOffset (batch + 1))).toBytes.map some)⟩ ∧
      CorrectionTripSuffix X g (pos + 2) o ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop pos).take 2) u :=
  correctionCuQReadsToUsedKInPrefix hp hX hb ht hFresh hWrites hr hSuffix (by decide)

omit hp hX hb in
/-- In a suffix containing a later event, the actual UsedK read preserves the row address
frame regardless of its returned value. -/
theorem correctionUsedKAddressFrame {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g pos batch : Nat} (hb : batch < p.batch)
    {t : TState} {F : List (Nat × Value)} {o : Option TState} {target : Event}
    (ht : At t 7959 ((8993, b64 (p.usedKBase + 4 * batch)) :: F))
    (hFresh : ∀ rv ∈ F, rv.1 ≠ 5959)
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) o)
    (hLate : 7959 < target.pc) (he : target ∈ (X.tr g).drop pos) :
    ∃ u vs, At u 7960 F ∧
      Walk kernel Assumptions.all l g u ((X.tr g).drop (pos + 1)) vs ∧
      target ∈ (X.tr g).drop (pos + 1) := by
  have hK := hp.alignment.2.2.2.2.2.2.2.2.2.1
  have hRange := hp.ranges ⟨p.usedKBase, 4 * p.batch⟩ (by simp [Params.inputRegions])
  change p.usedKBase + 4 * p.batch ≤ 2 ^ 64 at hRange
  let a : Acc := {loc := globalLoc (p.usedKBase + 4 * batch), size := 4}
  have hn : Next kernel Assumptions.all l g t t (.read a (afterLoad t [5959])) :=
    ⟨.refl, tripReadTemplate (l := l) (g := g) 2 ht (by simp [tripReadSite])
      (by simp [tripReadSite]; omega) (by simp [tripReadSite]; omega)⟩
  obtain ⟨e, u, hGet, ⟨bytes, _, rfl, heq⟩, hNext⟩ :=
    hn.continuing_at_nonempty (by rintro _ ⟨_, _, _, hNone⟩; cases hNone) hr
      (by intro h; rw [h] at he; cases he)
  obtain rfl := Option.some.inj heq
  have hDrop : (X.tr g).drop pos = ⟨t.pc, .rd a bytes⟩ :: (X.tr g).drop (pos + 1) := by
    apply List.ext_getElem?
    intro i
    cases i with
    | zero =>
      rw [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero]
      exact hGet
    | succ i => simp only [List.getElem?_drop, List.getElem?_cons_succ, Nat.add_assoc,
        Nat.add_comm 1 i]
  have hTarget : target ∈ (X.tr g).drop (pos + 1) := by
    rw [hDrop] at he
    rcases List.mem_cons.mp he with rfl | h
    · exact (Nat.not_lt_of_ge ht.1.le hLate).elim
    · exact h
  obtain ⟨vs, hw⟩ := walkFromRun hNext
  cases hBytes : rebuild 3 bytes with
  | error f =>
    have hFault : (afterLoad t [5959] bytes).fault = some f := by simp [afterLoad, hBytes]
    have hPc : (afterLoad t [5959] bytes).pc = 7959 := by simp [afterLoad, hBytes, ht.1]
    have hAt := faultWalkPc hFault hw hTarget
    omega
  | ok value =>
    have hState : afterLoad t [5959] bytes = next (setReg t 5959 value) := by
      rw [afterLoad_ok ht.2.1 ht.2.2.1 hBytes]
      simp [next, setReg, ht.2.1, ht.2.2.1]
    rw [hState] at hw
    exact ⟨_, vs, ((ht.mono ht.2.2.2.2.2).set hFresh).mono
      ((ht.mono ht.2.2.2.2.2).set hFresh).2.2.2.2.2, hw, hTarget⟩

/-- The selected request's UsedK load is observable at the head of its suffix. -/
theorem correctionUsedKLoadInPrefix {t : TState} {o : Option TState}
    (ht : At t 7959 [(8993, b64 (p.usedKBase + 4 * batch)), (1635, b32 (p.qLength batch)),
      (7276, b32 tile), (1634, b32 (p.qOffset batch))])
    (hUsedK : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4 * batch)).at k))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) o) (hMore : (X.tr g).drop pos ≠ []) :
    X.get (g, pos) = some ⟨7959, .rd {loc := globalLoc (p.usedKBase + 4 * batch), size := 4}
      ((b32 (p.kLength batch)).toBytes.map some)⟩ ∧
      ∃ u, u.pc = 7960 ∧ Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 1)) o := by
  have hK := hp.alignment.2.2.2.2.2.2.2.2.2.1
  have hRange := hp.ranges ⟨p.usedKBase, 4 * p.batch⟩ (by simp [Params.inputRegions])
  change p.usedKBase + 4 * p.batch ≤ 2 ^ 64 at hRange
  obtain ⟨he, hAt, hRun, _⟩ := tripReadTrace (addr := p.usedKBase + 4 * batch)
    (word := p.kLength batch) 2 ht (by simp [tripReadSite])
    (by simp [tripReadSite]; omega) (by simp [tripReadSite]; omega)
    (readsOfProtected (addr := p.usedKBase + 4 * batch + (tripReadSite 2).off) hX
      (hp.usedK batch hb) (by simpa [tripReadSite] using hUsedK))
    (by
      intro rv hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl <;> exact of_decide_eq_true rfl) hr hMore
  exact ⟨he, _, hAt.1, hRun⟩

section
variable {t : TState} {F : List (Nat × Value)} {o : Option TState}
    (ht : At t 7955 (correctionInputFacts p batch tile ++ F))
    (hFresh : ∀ rv ∈ F, rv.1 ∉ [1634, 5958, 5959])
    (hWrites : ((kernel.code.drop 7957).take 2).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hUsedK : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4 * batch)).at k))
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) o)
include ht hFresh hWrites hUsedK hr

/-- The correction lane loads both cumulative-query endpoints and its request's used-K
count from the protected launch inputs before computing visible KV trips. -/
theorem correctionTripReadsReachFromSuffix (hSuffix : CorrectionTripSuffix X g pos o) :
    ∃ u, At u 7960
        ([(5959, b32 (p.kLength batch)), (7276, b32 tile), (1635, b32 (p.qLength batch)),
          (1634, b32 (p.qOffset batch))] ++ F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 3)) o ∧
      X.get (g, pos) = some ⟨7955, .rd {loc := globalLoc (p.cuQBase + 4 * batch), size := 4}
        ((b32 (p.qOffset batch)).toBytes.map some)⟩ ∧
      X.get (g, pos + 1) = some ⟨7956,
        .rd {loc := globalLoc (p.cuQBase + 4 * (batch + 1)), size := 4}
          ((b32 (p.qOffset (batch + 1))).toBytes.map some)⟩ ∧
      X.get (g, pos + 2) = some ⟨7959, .rd {loc := globalLoc (p.usedKBase + 4 * batch), size := 4}
        ((b32 (p.kLength batch)).toBytes.map some)⟩ ∧
      CorrectionTripSuffix X g (pos + 3) o ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop pos).take 3) u := by

  have hK := hp.alignment.2.2.2.2.2.2.2.2.2.1
  have hKRange := hp.ranges ⟨p.usedKBase, 4 * p.batch⟩ (by simp [Params.inputRegions])
  change p.usedKBase + 4 * p.batch ≤ 2 ^ 64 at hKRange
  obtain ⟨b, hAt', hTail, he₀, he₁, hwSuffix, hPrefix⟩ :=
    correctionCuQReadsToUsedK hp hX hb ht hFresh hWrites hr hSuffix
  obtain ⟨he₂, hu, hU, hStep2⟩ := tripReadTrace (addr := p.usedKBase + 4 * batch)
    (word := p.kLength batch) 2 hAt' (by simp [tripReadSite])
    (by simp [tripReadSite]; omega) (by simp [tripReadSite]; omega)
    (readsOfProtected (addr := p.usedKBase + 4 * batch + (tripReadSite 2).off) hX
      (hp.usedK batch hb) (by simpa [tripReadSite] using hUsedK))
    (by
      intro pair hPair
      rcases List.mem_append.mp hPair with hBase | hFrame
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hBase
        rcases hBase with rfl | rfl | rfl | rfl <;> exact of_decide_eq_true rfl
      · intro he
        exact hFresh pair hFrame (by simp [tripReadSite] at he; simp [he])) hTail
    (tripSuffixNonempty hwSuffix hTail)
  have huSuffix := tripSuffixAdvance hwSuffix he₂ (show 7959 < 7960 by decide)
  refine ⟨_, hu.mono ⟨hu.2.2.2.2.1, hu.2.2.2.2.2.2.2.1, hu.2.2.2.2.2.2.1,
    hu.2.2.2.2.2.2.2.2.1, hu.2.2.2.2.2.2.2.2.2⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.add_assoc] using hU
  · exact he₀
  · exact he₁
  · simpa only [Nat.add_assoc, Nat.add_zero, tripReadSite] using he₂

  · simpa only [Nat.add_assoc] using huSuffix
  · have hSlice : ((X.tr g).drop pos).take 3 =
      ((X.tr g).drop pos).take 2 ++
        [⟨7959, .rd {loc := globalLoc (p.usedKBase + 4 * batch), size := 4}
          ((b32 (p.kLength batch)).toBytes.map some)⟩] := by
      apply List.ext_getElem?
      intro i
      have hLen : pos + 2 < (X.tr g).length := (List.getElem?_eq_some_iff.mp he₂).1
      have hDrop : 3 ≤ ((X.tr g).drop pos).length := by rw [List.length_drop]; omega
      have hTwo : (((X.tr g).drop pos).take 2).length = 2 := by
        rw [List.length_take, Nat.min_eq_left (by omega)]
      rcases (show i < 2 ∨ i = 2 ∨ 3 ≤ i by omega) with hi | rfl | hi
      · rw [List.getElem?_append_left (by simpa only [hTwo] using hi),
          List.getElem?_take_of_lt hi, List.getElem?_take_of_lt (by omega)]
      · rw [List.getElem?_append_right hTwo.le, hTwo, Nat.sub_self,
          List.getElem?_take_of_lt (by decide), List.getElem?_drop]
        rw [List.getElem?_cons_zero]
        exact he₂
      · rw [List.getElem?_eq_none (by rw [List.length_take]; omega),
          List.getElem?_eq_none (by simp [hTwo]; omega)]
    rw [hSlice]
    exact hPrefix.append (.event hStep2 (.refl _))

/-- The correction lane loads both cumulative-query endpoints and its request's used-K
count from the protected launch inputs before computing visible KV trips. -/
theorem correctionTripReadsFromSuffix (hSuffix : CorrectionTripSuffix X g pos o) :
    ∃ u, At u 7960
        ([(5959, b32 (p.kLength batch)), (7276, b32 tile), (1635, b32 (p.qLength batch)),
          (1634, b32 (p.qOffset batch))] ++ F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 3)) o ∧
      X.get (g, pos) = some ⟨7955, .rd {loc := globalLoc (p.cuQBase + 4 * batch), size := 4}
        ((b32 (p.qOffset batch)).toBytes.map some)⟩ ∧
      X.get (g, pos + 1) = some ⟨7956,
        .rd {loc := globalLoc (p.cuQBase + 4 * (batch + 1)), size := 4}
          ((b32 (p.qOffset (batch + 1))).toBytes.map some)⟩ ∧
      X.get (g, pos + 2) = some ⟨7959, .rd {loc := globalLoc (p.usedKBase + 4 * batch), size := 4}
        ((b32 (p.kLength batch)).toBytes.map some)⟩ ∧
      CorrectionTripSuffix X g (pos + 3) o := by
  obtain ⟨u, hu, hU, h0, h1, h2, hSuffix, _⟩ :=
    correctionTripReadsReachFromSuffix hp hX hb ht hFresh hWrites hUsedK hr hSuffix
  exact ⟨u, hu, hU, h0, h1, h2, hSuffix⟩
end

omit hp hX hb in
/-- A maximal correction lane performs all three protected selected-request metadata reads. -/
theorem openingTripReadsOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch tile : Nat} (hg : g < l.threads) (hb : batch < p.batch) {F : List (Nat × Value)}
    (c : OpeningTripCursor l X g 7955 (correctionInputFacts p batch tile ++ F))
    (hFresh : ∀ rv ∈ F, rv.1 ∉ [1634,5958,5959])
    (hWrites : ((kernel.code.drop 7957).take 2).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hCuQ : ∀ idx ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase+4*idx)).at k))
    (hUsedK : ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase+4*batch)).at k)) :
    Nonempty (OpeningTripCursor l X g 7960
      ([(5959,b32 (p.kLength batch)),(7276,b32 tile),(1635,b32 (p.qLength batch)),
        (1634,b32 (p.qOffset batch))] ++ F)) := by
  have hQ := hp.alignment.2.2.2.2.2.2.2.2.1
  have hCuRange := hp.ranges ⟨p.cuQBase,4*(p.batch+1)⟩ (by simp [Params.inputRegions])
  change p.cuQBase+4*(p.batch+1) ≤ 2^64 at hCuRange
  let a := p.cuQBase+4*batch
  have hQ0 : a+(tripReadSite 0).off = p.cuQBase+4*batch := rfl
  have hQ1 : a+(tripReadSite 1).off = p.cuQBase+4*(batch+1) := by dsimp [a,tripReadSite]; omega
  have fresh0 (pair : Nat × Value) (hm : pair ∈ correctionInputFacts p batch tile ++ F) :
      pair.1 ≠ (tripReadSite 0).dst := by
    rcases List.mem_append.mp hm with hm | hm
    · simp only [correctionInputFacts,List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl <;> exact of_decide_eq_true rfl
    · intro he
      exact hFresh pair hm (by simp [tripReadSite] at he; simp [he])
  obtain ⟨v⟩ := tripReadOfMaximal hMax hg 0 c (addr := a)
    (by simp [tripReadSite,correctionInputFacts,a])
    (by rw [hQ0]; omega) (by rw [hQ0]; omega) (by rw [hQ0]; exact hp.cuQ _ hb.le)
    (by rw [hQ0]; exact hCuQ batch hb.le) fresh0
  have fresh1 (pair : Nat × Value) (hm : pair ∈ (1634,b32 (p.qOffset batch)) ::
      correctionInputFacts p batch tile ++ F) : pair.1 ≠ (tripReadSite 1).dst := by
    rcases List.mem_cons.mp hm with rfl | hm
    · exact of_decide_eq_true rfl
    · rcases List.mem_append.mp hm with hm | hm
      · simp only [correctionInputFacts,List.mem_cons,List.not_mem_nil,or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl <;> exact of_decide_eq_true rfl
      · intro he
        exact hFresh pair hm (by simp [tripReadSite] at he; simp [he])
  obtain ⟨w⟩ := tripReadOfMaximal hMax hg 1 v (addr := a)
    (by simp [tripReadSite,correctionInputFacts,a])
    (by rw [hQ1]; omega) (by rw [hQ1]; omega) (by rw [hQ1]; exact hp.cuQ _ hb)
    (by rw [hQ1]; exact hCuQ (batch+1) hb) fresh1
  have hw := w.checkpoint
  have hOld := (holds_append _ _ _).1 hw.2.2.2.2.2.2
  obtain ⟨b,hLocal,hAt⟩ := usedKPointer hp g hb _
    (hw.mono ⟨hw.2.2.2.2.1,hw.2.2.2.2.2.1,hOld.1⟩)
  have hCore := afterFirstWords hw.1 hLocal
  have hFrame : ∀ r ∈ F.map Prod.fst, b.regs r = w.ready.regs r :=
    fun _ hm => schedulerLocalFrame (lo := 7957) (len := 2) hWrites
      (by set_option maxRecDepth 100000 in kernel_rfl) hLocal
      (show 7957 ≤ w.ready.pc by rw [hw.1]; decide)
      (by rw [hw.1]; exact Nat.le_refl _) hm
  have hSaved := holdsSchedulerFrame hOld.2 hFrame (fun _ hm => List.mem_map_of_mem hm)
  let K := [(8993,b64 (p.usedKBase+4*batch)),(1635,b32 (p.qLength batch)),
    (7276,b32 tile),(1634,b32 (p.qOffset batch))] ++ F
  have hAt' : At b 7959 K :=
    hAt.mono ((holds_append _ _ _).2 ⟨hAt.2.2.2.2,hSaved⟩)
  let u : OpeningTripCursor l X g 7959 K :=
    ⟨w.pos,w.before,b,w.ending,w.positive,w.bounded,w.released,hAt',w.recorded,w.remaining,
      w.localSteps.trans (run_rtg hCore)⟩
  have hK := hp.alignment.2.2.2.2.2.2.2.2.2.1
  have hRange := hp.ranges ⟨p.usedKBase,4*p.batch⟩ (by simp [Params.inputRegions])
  change p.usedKBase+4*p.batch ≤ 2^64 at hRange
  have fresh2 (pair : Nat × Value) (hm : pair ∈ K) : pair.1 ≠ (tripReadSite 2).dst := by
    rcases List.mem_append.mp hm with hm | hm
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl <;> exact of_decide_eq_true rfl
    · intro he
      exact hFresh pair hm (by simp [tripReadSite] at he; simp [he])
  obtain ⟨last⟩ := tripReadOfMaximal hMax hg 2 u (addr := p.usedKBase+4*batch)
    (word := p.kLength batch)
    (by simp [tripReadSite,K]) (by simp [tripReadSite]; omega) (by simp [tripReadSite]; omega)
    (by change HasValue m (globalLoc (p.usedKBase+4*batch)) _; exact hp.usedK batch hb)
    (by simpa [tripReadSite] using hUsedK) fresh2
  have hh := last.checkpoint.2.2.2.2
  exact ⟨{ pos := last.pos
           before := last.before
           ready := last.ready
           ending := last.ending
           positive := last.positive
           bounded := last.bounded
           released := last.released
           checkpoint := last.checkpoint.mono ⟨hh.1,hh.2.2.2.1,hh.2.2.1,hh.2.2.2.2⟩
           recorded := last.recorded
           remaining := last.remaining
           localSteps := last.localSteps }⟩

end
end PTX.Kernels.TmlFa4Fwd.Correction
