-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Spec
public import Kernels.TmlFa4Fwd.Proof.PrologueBroadcast
public import Core.Sync.Aligned
import Kernels.TmlFa4Fwd.Proof.Thread.MmaResourceOrder
import Kernels.TmlFa4Fwd.Proof.MmaResources
import Kernels.TmlFa4Fwd.Proof.Thread.StatisticsAllocationExclusion
import Kernels.TmlFa4Fwd.Proof.MmaQueryStartupPrefix
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Kernels.TmlFa4Fwd.Flow.Code.Part043
import Kernels.TmlFa4Fwd.Flow.Code.Part143
public import Lemmas.Flow.NotTcData
import Lemmas.Flow.Resource
import Lemmas.Flow.CountTake
import Lemmas.Flow.Final

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof Mma Prologue

private def allocatorEvent (l : Launch) (g : Nat) (rank : Fin 3) : Event :=
  match rank.val with
  | 0 => ⟨1909, .tc (.resource .one (some (allocationSlot l g)) (.alloc 512))⟩
  | 1 => ⟨2763, .tc (.resource .one none .relinquish)⟩
  | _ => ⟨2766, .tc (.resource .one none (.dealloc 0 512))⟩

private theorem allocatorEvent_pc_strict (l : Launch) (g : Nat) (a b : Fin 3)
    (h : (allocatorEvent l g a).pc < (allocatorEvent l g b).pc) :
    a.val < b.val := by
  fin_cases a <;> fin_cases b <;> simp [allocatorEvent] at h ⊢

set_option maxRecDepth 100000 in
private theorem allocatorNoEarlyData :
    (kernel.code.take 3103).all (fun i => !tcDataOp i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem allocatorNoOtherData :
    registerHintSites.all (fun pc => match kernel.code[pc]? with
      | some i => !tcDataOp i.op
      | none => false) = true := by kernel_rfl

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem noDataCollectiveAboveArithmetic {g j : Nat} (hw : 12 ≤ warpIndex l g) {e : Event}
    (he : X.get (g,j) = some e) (hData : isTcData e = true) : False := by
  rcases get_source hX he with ⟨_, hf⟩ | ⟨_, ins, _, _, hc, hf⟩
  · simp [hf, isTcData] at hData
  have hOp := fires_tcData_op hf hData
  by_cases hEarly : e.pc < 3103
  · have hGet : (kernel.code.take 3103)[e.pc]? = some ins :=
      (List.getElem?_take_of_lt hEarly).trans hc
    have hFalse := List.all_eq_true.mp allocatorNoEarlyData ins (List.mem_of_getElem? hGet)
    simp [hOp] at hFalse
  by_cases hHint : e.pc ∈ registerHintSites
  · have hFalse := List.all_eq_true.mp allocatorNoOtherData _ hHint
    rw [hc] at hFalse
    simp [hOp] at hFalse
  have hRole := roleBodyPcOfEvent hp hX he (by omega) hHint
  change roleBodyPc (warpIndex l g) e.pc at hRole
  unfold roleBodyPc at hRole
  have hExit : e.pc = 9205 := hRole.resolve_right (by
    intro hBody
    split_ifs at hBody <;> omega)
  rw [hExit, Flow.code_9205] at hc
  obtain rfl := Option.some.inj hc
  cases hOp

private theorem mmaCollectiveShape {g j : Nat} (hw : warpIndex l g = 12) {e : Event}
    (he : X.get (g,j) = some e) (hColl : isTcColl e = true) :
    ∃ rank, e = allocatorEvent l g rank := by
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp only [isTcColl, Bool.false_eq_true] at hColl
  rename_i tc
  cases tc <;> try contradiction
  all_goals try exact (noDataCollectiveAboveArithmetic hp hX (hw ▸ le_rfl) he rfl).elim
  rename_i group dst action
  obtain ⟨rfl, hAlloc | hRel | hDealloc⟩ := actualResourceRequest hX he
  · obtain ⟨rfl, rfl⟩ := hAlloc
    obtain ⟨_, _, rfl, _⟩ := allocatorIssueAtEntryAllLanes hp hX he
    exact ⟨0, rfl⟩
  · obtain ⟨rfl, rfl⟩ := hRel
    rcases get_source hX he with ⟨_, hf⟩ | ⟨_, ins, _, _, hc, hf⟩
    · cases hf
    rw [Flow.code_2763] at hc
    obtain rfl := Option.some.inj hc
    obtain ⟨_, rfl, _⟩ := fires_tcRelinquish_resource hf rfl
    exact ⟨1, rfl⟩
  · obtain ⟨rfl, base, rfl⟩ := hDealloc
    obtain rfl := mmaDeallocReturnsZero hp hX he
    rcases get_source hX he with ⟨_, hf⟩ | ⟨_, ins, _, _, hc, hf⟩
    · cases hf
    rw [Flow.code_2766] at hc
    obtain rfl := Option.some.inj hc
    obtain ⟨_, rfl, _⟩ := fires_tcDealloc_resource hf rfl
    exact ⟨2, rfl⟩

/-- Every Tensor Memory resource request belongs to the allocator warp. -/
theorem tensorResourceIssuerWarp {g j : Nat} {e : Event} {group : CtaGroup} {dst : Option Loc}
    {act : Tmem.Request} (he : X.get (g,j) = some e)
    (hKind : e.kind = .tc (.resource group dst act)) :
    warpIndex l g = 12 := by
  obtain ⟨pc, kind⟩ := e
  change kind = _ at hKind
  subst kind
  have hResource := (actualResourceRequest hX he).2
  have hSite : pc = 1909 ∨ pc = 2763 ∨ pc = 2766 := by
    rcases hResource with ⟨ha, _⟩ | ⟨hr, _⟩ | ⟨hd, _⟩
    · exact .inl ha
    · exact .inr (.inl hr)
    · exact .inr (.inr hd)
  have hLate : 173 < pc := by rcases hSite with h | h | h <;> omega
  have hHint : pc ∉ registerHintSites := by rcases hSite with rfl | rfl | rfl <;> decide
  have hRole := roleBodyPcOfEvent hp hX he hLate hHint
  change roleBodyPc (warpIndex l g) pc at hRole
  unfold roleBodyPc at hRole
  rcases hRole with hExit | hBody
  · rcases hSite with h | h | h <;> omega
  · split_ifs at hBody <;> (rcases hSite with h | h | h <;> omega)

/-- Arithmetic roles use the data collectives of Tensor Memory. -/
theorem arithmeticTensorCollectiveIsData {g j : Nat} (hw : warpIndex l g < 12) {e : Event}
    (he : X.get (g,j) = some e) (hColl : isTcColl e = true) :
    isTcData e = true := by
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp only [isTcColl, Bool.false_eq_true] at hColl
  rename_i tc
  cases tc <;> try contradiction
  all_goals first | rfl | exact (Nat.ne_of_lt hw (tensorResourceIssuerWarp hp hX he rfl)).elim

/-- The loader and epilogue warps issue no Tensor Memory collective. -/
theorem noLoaderOrEpilogueTensorCollective {g j k : Nat} (hw : 13 ≤ warpIndex l g) :
    ¬ X.TcK (g,j) k := by
  rintro ⟨⟨⟨pc, kind⟩, he, hColl⟩, _⟩
  cases kind <;> simp only [isTcColl, Bool.false_eq_true] at hColl
  rename_i tc
  cases tc <;> try contradiction
  all_goals try exact noDataCollectiveAboveArithmetic hp hX (by omega) he rfl
  have := tensorResourceIssuerWarp hp hX he rfl
  omega

private theorem mmaCollectiveOrder {g i j : Nat} (hOrder : i < j) {a b : Fin 3}
    (hi : X.get (g,i) = some (allocatorEvent l g a))
    (hj : X.get (g,j) = some (allocatorEvent l g b)) :
    (allocatorEvent l g a).pc < (allocatorEvent l g b).pc := by
  fin_cases a
  · have hi6 := (allocatorIssueAtEntryAllLanes hp hX hi).1
    fin_cases b
    · have hj6 := (allocatorIssueAtEntryAllLanes hp hX hj).1
      omega
    · change 1909 < 2763; decide
    · change 1909 < 2766; decide
  · exact tailPrecedesHigherSite hp hX hi hj hOrder (.inl rfl)
  · exact tailPrecedesHigherSite hp hX hi hj hOrder (.inr rfl)

private theorem mmaCollectivePrefixNodup {g j : Nat} (hw : warpIndex l g = 12) :
    (((X.tr g).take j).filter isTcColl).Nodup := by
  let xs := ((X.tr g).take j).filter isTcColl
  have hOrd : xs.Pairwise (fun a b => a.pc < b.pc) := by
    apply List.pairwise_filter.mpr
    rw [List.pairwise_iff_getElem]
    intro a b ha hb hab hA hB
    have ha' : a < j := lt_of_lt_of_le ha (List.length_take_le ..)
    have hb' : b < j := lt_of_lt_of_le hb (List.length_take_le ..)
    have haGet : X.get (g,a) = some ((X.tr g).take j)[a] :=
      (List.getElem?_take_of_lt ha').symm.trans (List.getElem?_eq_getElem ha)
    have hbGet : X.get (g,b) = some ((X.tr g).take j)[b] :=
      (List.getElem?_take_of_lt hb').symm.trans (List.getElem?_eq_getElem hb)
    obtain ⟨a', hA'⟩ := mmaCollectiveShape hp hX hw haGet hA
    obtain ⟨b', hB'⟩ := mmaCollectiveShape hp hX hw hbGet hB
    rw [hA', hB']
    exact mmaCollectiveOrder hp hX hab (hA' ▸ haGet) (hB' ▸ hbGet)
  exact List.nodup_iff_pairwise_ne.mpr
    (hOrd.imp (fun h hEq => (Nat.ne_of_lt h) (congrArg Event.pc hEq)))

private theorem mmaCollectivePrefixUpper {g j : Nat} (hw : warpIndex l g = 12) (rank : Fin 3)
    (hj : X.get (g,j) = some (allocatorEvent l g rank)) :
    ((X.tr g).take j).countP isTcColl ≤ rank.val := by
  let codes := [allocatorEvent l g 0, allocatorEvent l g 1, allocatorEvent l g 2]
  let xs := ((X.tr g).take j).filter isTcColl
  have hNo := mmaCollectivePrefixNodup hp hX (j := j) hw
  have hSubset : xs ⊆ codes.take rank.val := by
    intro e hm
    obtain ⟨hMem, hColl⟩ := List.mem_filter.mp hm
    obtain ⟨i,hGet⟩ := List.mem_iff_getElem?.mp hMem
    have hi : i < j := ((List.getElem?_eq_some_iff.mp hGet).1).trans_le
      (List.length_take_le ..)
    rw [List.getElem?_take_of_lt hi] at hGet
    obtain ⟨a, rfl⟩ := mmaCollectiveShape hp hX hw hGet hColl
    have ha := allocatorEvent_pc_strict l g a rank (mmaCollectiveOrder hp hX hi hGet hj)
    apply List.mem_of_getElem? (i := a.val)
    rw [List.getElem?_take_of_lt ha]
    fin_cases a <;> rfl
  rw [List.countP_eq_length_filter]
  exact (hNo.length_le_of_subset hSubset).trans (List.length_take_le ..)

private theorem earlierOpeningOfTail {g j : Nat} (hw : warpIndex l g = 12) {e : Event}
    (he : X.get (g,j) = some e) (hLate : 1911 < e.pc) :
    6 < j ∧ X.get (g,6) = some (allocatorEvent l g 0) := by
  have hThread := event_thread_lt hX he
  obtain ⟨_, _, _, _, _, hRead, hBefore, _, _⟩ := allocationReadBeforeEvent hp hX he hw hLate
  obtain ⟨n, _, _, _, hAlloc, _⟩ := allocationPrefixAtBarrierReadOrExit hp hX hThread hw hRead
    (.inr (.inr rfl))
  have hn := (allocatorIssueAtEntryAllLanes hp hX hAlloc).1
  subst n
  refine ⟨?_, hAlloc⟩
  unfold allocationBarrierPos at hBefore
  split at hBefore <;> omega

private theorem mmaCollectivePrefixExact {g j : Nat} (hw : warpIndex l g = 12) (rank : Fin 3)
    (he : X.get (g,j) = some (allocatorEvent l g rank)) :
    ((X.tr g).take j).countP isTcColl = rank.val := by
  have hUpper := mmaCollectivePrefixUpper hp hX hw rank he
  fin_cases rank
  · exact Nat.eq_zero_of_le_zero hUpper
  · obtain ⟨hBefore, hAlloc⟩ := earlierOpeningOfTail hp hX hw he (show 1911 < 2763 by decide)
    have hCount := countP_take_succ (p := isTcColl) hAlloc rfl
    have hMono := countP_take_mono isTcColl (X.tr g) (show 6+1 ≤ j by omega)
    change ((X.tr g).take j).countP isTcColl ≤ 1 at hUpper
    change ((X.tr g).take j).countP isTcColl = 1
    omega
  · obtain ⟨k, hk, hRel⟩ := mmaRelinquishBeforeDealloc hp hX hw he
    obtain ⟨hBefore, hAlloc⟩ := earlierOpeningOfTail hp hX hw hRel (by decide)
    have hAllocCount := countP_take_succ (p := isTcColl) hAlloc rfl
    have hRelCount := countP_take_succ (p := isTcColl) hRel rfl
    have hAllocMono := countP_take_mono isTcColl (X.tr g) (show 6+1 ≤ k by omega)
    have hRelMono := countP_take_mono isTcColl (X.tr g) (show k+1 ≤ j by omega)
    change ((X.tr g).take j).countP isTcColl ≤ 2 at hUpper
    change ((X.tr g).take j).countP isTcColl = 2
    omega

/-- An exited allocator lane has executed all Tensor Memory collectives of its warp. -/
theorem mmaExitCollectiveCount {g j pc : Nat} (hw : warpIndex l g = 12)
    (he : X.get (g,j) = some ⟨pc, .exit⟩) :
    (X.tr g).countP isTcColl = 3 := by
  obtain ⟨i, hi, hDealloc⟩ := mmaDeallocBeforeExit hp hX hw he
  have hPrefix := mmaCollectivePrefixExact hp hX hw 2 hDealloc
  have hCount := countP_take_succ (p := isTcColl) hDealloc rfl
  have hLower : 3 ≤ (X.tr g).countP isTcColl := by
    have hMono := (List.take_sublist (i+1) (X.tr g)).countP_le (p := isTcColl)
    change ((X.tr g).take i).countP isTcColl = 2 at hPrefix
    omega
  have hNo := mmaCollectivePrefixNodup hp hX (j := (X.tr g).length) hw
  rw [List.take_length] at hNo
  let codes := [allocatorEvent l g 0, allocatorEvent l g 1, allocatorEvent l g 2]
  have hSubset : (X.tr g).filter isTcColl ⊆ codes := by
    intro e hm
    obtain ⟨hMem, hColl⟩ := List.mem_filter.mp hm
    obtain ⟨k, hGet⟩ := List.mem_iff_getElem?.mp hMem
    obtain ⟨rank, rfl⟩ := mmaCollectiveShape hp hX hw hGet hColl
    fin_cases rank <;> simp [codes]
  have hUpper := hNo.length_le_of_subset hSubset
  change ((X.tr g).filter isTcColl).length ≤ 3 at hUpper
  rw [← List.countP_eq_length_filter] at hUpper
  omega

omit hp hX in
/-- The ordinal of a Tensor Memory allocator request. -/
def mmaResourceOrdinal : Tmem.Request → Nat
  | .alloc _ => 0
  | .relinquish => 1
  | .dealloc .. => 2

/-- Allocation, permit relinquishment and deallocation have ordinals zero, one and two. -/
theorem mmaResourceCollectiveOrdinal {g j : Nat} (hw : warpIndex l g = 12) {e : Event}
    {group : CtaGroup} {dst : Option Loc} {req : Tmem.Request} (he : X.get (g,j) = some e)
    (hReq : e.kind = .tc (.resource group dst req)) :
    X.TcK (g,j) (mmaResourceOrdinal req) := by
  have hColl : isTcColl e = true := by cases e; simp_all [isTcColl]
  obtain ⟨rank, rfl⟩ := mmaCollectiveShape hp hX hw he hColl
  have hCount := mmaCollectivePrefixExact hp hX hw rank he
  refine ⟨⟨_, he, hColl⟩, ?_⟩
  rw [hCount]
  fin_cases rank <;> simp [allocatorEvent] at hReq ⊢
  all_goals rw [← hReq.2.2]; rfl

/-- No allocator lane issues a fourth Tensor Memory collective. -/
theorem mmaCollectiveOrdinalLtThree {g j k : Nat} (hw : warpIndex l g = 12) (hk : X.TcK (g,j) k) :
    k < 3 := by
  obtain ⟨⟨e, he, hMember⟩, hk⟩ := hk
  obtain ⟨rank, rfl⟩ := mmaCollectiveShape hp hX hw he hMember
  exact ((mmaCollectivePrefixExact hp hX hw rank he).symm.trans hk) ▸ rank.isLt

/-- Equal collective ordinals in the allocator warp agree on decoded instruction and operands. -/
theorem mmaCollectivesAgree {g h i j k : Nat} {e f : Event} (hw : warpIndex l g = 12)
    (hWarp : SameWarp l g h) (he : X.get (g,i) = some e) (hf : X.get (h,j) = some f)
    (hi : X.TcK (g,i) k) (hj : X.TcK (h,j) k) :
    e = f := by
  obtain ⟨⟨e', he', hEMem⟩, hi⟩ := hi
  obtain ⟨⟨f', hf', hFMem⟩, hj⟩ := hj
  obtain rfl := Option.some.inj (he.symm.trans he')
  obtain rfl := Option.some.inj (hf.symm.trans hf')
  have hw' : warpIndex l h = 12 := hWarp.2.symm.trans hw
  obtain ⟨a, rfl⟩ := mmaCollectiveShape hp hX hw he hEMem
  obtain ⟨b, rfl⟩ := mmaCollectiveShape hp hX hw' hf hFMem
  have ha := mmaCollectivePrefixExact hp hX hw a he
  have hb := mmaCollectivePrefixExact hp hX hw' b hf
  have hRank : a = b := Fin.ext (ha.symm.trans (hi.trans (hj.symm.trans hb)))
  subst b
  have hSlot : allocationSlot l g = allocationSlot l h := by
    unfold allocationSlot
    rw [hWarp.1.2.2]
  fin_cases a <;> simp [allocatorEvent, hSlot]

/-- An exited allocator peer has already covered the ordinal of each allocator collective. -/
theorem mmaCollectivePeerNotExitedShort {g h i j k : Nat} (hw : warpIndex l g = 12)
    (hWarp : SameWarp l g h) (hi : X.TcK (g,i) k) :
    ¬ X.ExitedShort isTcColl (h,j) k := by
  rintro ⟨⟨pc, he⟩, hEarly⟩
  have hCount := mmaExitCollectiveCount hp hX (hWarp.2.symm.trans hw) he
  have hBound := mmaCollectiveOrdinalLtThree hp hX hw hi
  change (X.tr h).countP isTcColl ≤ k at hEarly
  omega
end

/-- The remaining collective alignment facts for softmax and correction lanes. -/
structure ArithmeticTensorAlignment (l : Launch) (X : Execution) : Prop where
  sameOrdinal : ∀ {g h i j k : Nat} {e f : Event}, warpIndex l g < 12 → SameWarp l g h →
    X.get (g, i) = some e → X.get (h, j) = some f → X.TcK (g, i) k → X.TcK (h, j) k →
    e.pc = f.pc ∧ AlignedClass.tc.operands e.kind = AlignedClass.tc.operands f.kind
  exitCoverage : ∀ {g h i j k : Nat}, warpIndex l g < 12 → SameWarp l g h → X.TcK (g, i) k →
    ¬ X.ExitedShort isTcColl (h, j) k

/-- Any remaining Tensor Memory divergence or short exit comes from one of the arithmetic warps. -/
theorem alignedTensorOfArithmeticWarps {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hAligned : ArithmeticTensorAlignment l X) :
    ¬ (AlignedClass.tc.Divergent l kernel X ∨ AlignedClass.tc.Exited l kernel X) := by
  rintro (⟨⟨g,i⟩, ⟨h,j⟩, a, b, ke, kf, hWarp, he, hf, hEMem, hFMem, hK, _, hBad⟩ | hBad)
  · let k := ((X.tr g).take i).countP isTcColl
    have hE : X.TcK (g,i) k := ⟨⟨_, he, hEMem⟩, rfl⟩
    have hF : X.TcK (h,j) k := ⟨⟨_, hf, hFMem⟩, hK.symm⟩
    by_cases hw : warpIndex l g < 12
    · obtain ⟨hPc, hOps⟩ := hAligned.sameOrdinal hw hWarp he hf hE hF
      exact hBad.elim (fun h => h hPc) (fun h => h hOps)
    · by_cases h12 : warpIndex l g = 12
      · have hEq := mmaCollectivesAgree hp hX h12 hWarp he hf hE hF
        exact hBad.elim (fun h => h (congrArg Event.pc hEq))
          (fun h => h (congrArg (AlignedClass.tc.operands ∘ Event.kind) hEq))
      · exact noLoaderOrEpilogueTensorCollective hp hX (by omega) hE
  · obtain ⟨⟨g,i⟩, ⟨h,j⟩, k, hWarp, hk, hEarly⟩ := (AlignedClass.exited_tc_iff l).mp hBad
    by_cases hw : warpIndex l g < 12
    · exact hAligned.exitCoverage hw hWarp hk hEarly
    · by_cases h12 : warpIndex l g = 12
      · exact mmaCollectivePeerNotExitedShort hp hX h12 hWarp hk hEarly
      · exact noLoaderOrEpilogueTensorCollective hp hX (by omega) hk

end PTX.Kernels.TmlFa4Fwd.Thread
