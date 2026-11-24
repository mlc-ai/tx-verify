-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringPageIndex
public import Kernels.TmlFa4Fwd.Proof.LoaderPageScratch
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

structure RecurringPageReadSite where
  pc : Nat
  base : Nat
  address : Nat

/-- The live page-table arms add the quotient to the selected batch's row of the table. -/
def recurringPageReadSite : Fin 2 → RecurringPageReadSite
  | 0 => ⟨946, 7648, 7650⟩
  | 1 => ⟨1416, 7763, 7765⟩

def recurringPageReadInput (p : Params) (site : Fin 2) (batch row : Nat) :
    List (Nat × Value) :=
  [((recurringPageSite site).pageIndex, b32 (row / 16)),
   ((recurringPageReadSite site).base, b64 (p.pageTableBase + 4 * (batch * p.pageTableStride)))]

private theorem recurringPageByteInTable {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {batch row byte : Nat} (hb : batch < p.batch) (hr : row < p.kLength batch) (hk : byte < 4) :
    (⟨p.pageTableBase, 4 * p.batch * p.pageTableStride⟩ : Region).Contains
      ((globalLoc (pageWordAddress p batch (row / 16))).at byte) := by
  have hStride := (hp.pageTable batch hb).1
  have hIndex : row / 16 < p.pageTableStride := by omega
  have hEnd := Nat.mul_le_mul_right p.pageTableStride (show batch + 1 ≤ p.batch by omega)
  rw [Nat.add_mul, Nat.one_mul] at hEnd
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp only [Loc.at, globalLoc, pageWordAddress, Nat.mul_assoc]
  all_goals omega

private theorem recurringPageAddressBound {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {batch row : Nat} (hb : batch < p.batch) (hr : row < p.kLength batch) :
    pageWordAddress p batch (row / 16) < 2 ^ 64 := by
  have hRange := hp.ranges ⟨p.pageTableBase, 4 * p.batch * p.pageTableStride⟩
    (by simp [Params.inputRegions])
  obtain ⟨_, _, _, hEnd⟩ := recurringPageByteInTable hp hb hr (byte := 0) (by decide)
  change pageWordAddress p batch (row / 16) + 0 < _ at hEnd
  rw [Nat.add_zero] at hEnd
  exact hEnd.trans_le hRange

private theorem recurringPageAddressCore {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g batch row : Nat} (hb : batch < p.batch) (hr : row < p.kLength batch) (site : Fin 2) :
    Seg kernel [] l g 2 ((recurringPageReadSite site).pc - 2)
      (recurringPageReadInput p site batch row) (recurringPageReadSite site).pc
      [((recurringPageReadSite site).address, b64 (pageWordAddress p batch (row / 16)))] := by
  let index := row / 16
  have hLen := (hp.lengths batch hb).2.2
  have h31 : index < 2 ^ 31 := by omega
  have h32 : index < 2 ^ 32 := by omega
  have hAddr : pageWordAddress p batch index < 2 ^ 64 := recurringPageAddressBound hp hb hr
  have hAdd : p.pageTableBase + 4 * (batch * p.pageTableStride) + 4 * index =
      pageWordAddress p batch index := by simp [pageWordAddress, Nat.mul_add, Nat.add_assoc]
  have hBase : p.pageTableBase + 4 * (batch * p.pageTableStride) < 2 ^ 64 := by omega
  have hOff : 4 * index < 2 ^ 64 := by omega
  have hSigned : toSigned 32 (BitVec.ofNat 64 index) = (index : Int) := by
    simp only [toSigned, toNat_ofNat_lt (show index < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt h32, ite_eq_left h31]
  have hI4 : toSigned 32 (truncBits 32 (BitVec.ofInt 64 4)) = 4 := rfl
  have hMul : (index : Int) * 4 = ((4 * index : Nat) : Int) := by push_cast; omega
  fin_cases site <;> intro t ht <;>
    simp only [recurringPageReadSite, recurringPageReadInput, recurringPageSite] at ht ⊢ <;>
    seg_fp ht using
      simp only [← show index = row / 16 from rfl,
        b64, kind_s_beq_s, ↓reduceIte, hI4, hSigned, truncBits_ofNat h32 (by decide),
        truncBits_ofNat hOff (by decide), truncBits_ofNat hBase (by decide), hMul,
        BitVec.ofInt_natCast, ← BitVec.ofNat_add, hAdd, truncBits_ofNat hAddr (by decide)]

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g i batch row : Nat} (hb : batch < p.batch) (hr : row < p.kLength batch) (site : Fin 2)
    {t : TState} {F : List (Nat × Value)}
    (hKeep : ((kernel.code.drop ((recurringPageReadSite site).pc - 2)).take 2).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hFresh : ∀ pair ∈ F, pair.1 ≠ (recurringPageSite site).physicalPage)
    (ht : At t ((recurringPageReadSite site).pc - 2) (recurringPageReadInput p site batch row ++ F))
include hp hX hFrame hb hr site hKeep hFresh ht

/-- An actual load in either live page-table arm returns the launch's physical page.
The output frame establishes immutable source bytes for this read. -/
theorem recurringPageReadObservedInPrefixWithFrame {o : Option TState}
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop i) o) (hSeen : i < (X.tr g).length) :
    let s := recurringPageReadSite site
    let addr := pageWordAddress p batch (row / 16)
    let word := b32 (p.page batch (row / 16))
    let dst := (recurringPageSite site).physicalPage
    ∃ u, X.get (g, i) = some ⟨s.pc, .rd {loc := globalLoc addr, size := 4}
        (word.toBytes.map some)⟩ ∧
      At u (s.pc + 1) ((dst, word) :: F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (i + 1)) o := by
  dsimp only
  let s := recurringPageReadSite site
  let addr := pageWordAddress p batch (row / 16)
  let word := b32 (p.page batch (row / 16))
  let dst := (recurringPageSite site).physicalPage
  let a : Acc := {loc := globalLoc addr, size := 4}
  have hFrames := (holds_append ..).mp ht.2.2.2.2
  obtain ⟨v, hv, hV⟩ := recurringPageAddressCore hp (g := g) hb hr site t (ht.mono hFrames.1)
  have hLo : 174 ≤ s.pc - 2 := by fin_cases site <;> decide
  have hHi : s.pc - 2 + 2 ≤ 1906 := by fin_cases site <;> decide
  have hRange : 174 ≤ s.pc ∧ s.pc < 1906 := by fin_cases site <;> decide
  have hSeq : ((kernel.code.drop (s.pc - 2)).take 1).all
      (fun ins => Epilogue.schedulerFallsThrough ins.op) = true := by
    fin_cases site <;> (set_option maxRecDepth 100000 in kernel_rfl)
  obtain ⟨hvA, hVF⟩ := loaderLinear hLo hHi ht.1 hKeep hSeq hv
  have hCode : kernel.code[s.pc]? = some ⟨none, .mem
    {kind := .load, space := some .global, sem := .weak, elem := .int .b 32,
     addr := ⟨.reg s.address 64, 0⟩, dsts := [some dst]}⟩ := by
    fin_cases site
    · exact Flow.code_946
    · exact Flow.code_1416
  have hAddr : addr < 2 ^ 64 := recurringPageAddressBound hp hb hr
  have hAlign : addr % 4 = 0 := by
    have := hp.alignment.2.2.2.2.2.2.2.2.2.2.1
    dsimp [addr, pageWordAddress]
    omega
  have hNext : Next kernel Assumptions.all l g t v (.read a (afterLoad v [dst])) := by
    refine ⟨run_rtg hvA, ?_⟩
    rw [loaderOutCore (by rw [hV.1]; exact hRange.1) (by rw [hV.1]; exact hRange.2)]
    rw [out_event hV.2.2.2.1 (by rw [hV.1]; exact hCode) rfl rfl]
    change Out.ev (loadTmpl [] l g v .global false 32 [dst] s.address 0) = _
    exact congrArg Out.ev (loadTmpl_global hV.2.1 hV.2.2.2.2.1 hAddr (by decide) hAlign)
  obtain ⟨_, _, he, ⟨bs, _, rfl, hAfter⟩, hTail⟩ := hNext.continuing_at_nonempty (by
    rintro e ⟨_, _, _, hBad⟩
    cases hBad) hRun (fun hEmpty => (Nat.not_le_of_lt hSeen) (List.drop_eq_nil_iff.mp hEmpty))
  obtain rfl := Option.some.inj hAfter
  rw [hV.1] at he
  have hMem : X.MemReads (.thread (g, i)) a bs := .inl ⟨s.pc, he⟩
  have hi : row / 16 < (p.kLength batch + 15) / 16 := by omega
  have hBytes : bs = word.toBytes.map some := by
    apply hX.launch_value hMem rfl
    · intro k hk w target bytes hw
      exact hFrame.input_unwritten hp (by simp [Params.inputRegions])
        (recurringPageByteInTable hp hb hr hk) hw
    · exact hp.pageBytes batch hb (row / 16) hi
  subst bs
  have hRebuild := PTX.Proof.rebuild_scalar (v := word) (show 0 < 4 by decide) rfl
  have hRest : afterLoad v [dst] (word.toBytes.map some) = next (setReg v dst word) := by
    rw [afterLoad_ok hV.2.1 hV.2.2.1 hRebuild]
    simp [next, setReg, hV.2.1, hV.2.2.1]
  rw [hRest] at hTail
  have hVRegs := Epilogue.holdsSchedulerFrame hFrames.2 hVF (fun _ h => List.mem_map_of_mem h)
  exact ⟨_, he, (hV.mono hVRegs).set hFresh, hTail⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
