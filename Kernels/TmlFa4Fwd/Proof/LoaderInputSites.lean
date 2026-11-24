-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.InputCopies
public import Kernels.TmlFa4Fwd.Proof.LoaderCopyCommit
public import Kernels.TmlFa4Fwd.Flow.Code.Part011
public import Kernels.TmlFa4Fwd.Flow.Code.Part012
public import Kernels.TmlFa4Fwd.Flow.Code.Part018
public import Kernels.TmlFa4Fwd.Flow.Code.Part021
public import Lemmas.Flow.TensorLoadFacts

public import Lemmas.Step.Released
import Lemmas.Step.CpAsyncIssueProgress
import Lemmas.Step.DrainInOrder
import Kernels.TmlFa4Fwd.Assumptions.WellFormed

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The operand registers and CTA-local offsets at a decoded Q or Bias load. -/
structure InputSite where
  pc : Nat
  sharedOffset : Nat
  mapReg : Nat
  colReg : Nat
  rowReg : Nat
  barrierReg : Nat
  barrierOffset : Nat
  policyReg : Nat
  bias : Bool

def inputSite : Fin 14 → InputSite
  | 0 => ⟨693, 3072, 7580, 1894, 1087, 2535, 0, 7581, false⟩
  | 1 => ⟨700, 19456, 7582, 1896, 1087, 2535, 0, 7583, false⟩
  | 2 => ⟨719, 166912, 7585, 1903, 1087, 1114, 0, 7586, true⟩
  | 3 => ⟨727, 183296, 7587, 1906, 1087, 1114, 0, 7588, true⟩
  | 4 => ⟨745, 35840, 7590, 1913, 1912, 2535, 8, 7591, false⟩
  | 5 => ⟨753, 52224, 7592, 1916, 1915, 2535, 8, 7593, false⟩
  | 6 => ⟨771, 199680, 7595, 1922, 1115, 2535, 328, 7596, true⟩
  | 7 => ⟨779, 216064, 7597, 1924, 1115, 2535, 328, 7598, true⟩
  | 8 => ⟨1163, 166912, 7699, 2046, 1087, 1140, 0, 7700, true⟩
  | 9 => ⟨1173, 183296, 7701, 2051, 1087, 1140, 0, 7702, true⟩
  | 10 => ⟨1191, 199680, 7704, 2057, 2058, 2535, 328, 7705, true⟩
  | 11 => ⟨1200, 216064, 7706, 2061, 2062, 2535, 328, 7707, true⟩
  | 12 => ⟨1376, 166912, 7754, 2125, 1087, 1142, 0, 7755, true⟩
  | 13 => ⟨1383, 183296, 7756, 2127, 1087, 1142, 0, 7757, true⟩

theorem inputSiteCode (i : Fin 14) :
    let s := inputSite i
    kernel.code[s.pc]? = some ⟨none, .cpTensor false false 2535 s.sharedOffset
      (.reg s.mapReg) [.reg s.colReg, .reg s.rowReg, .reg 7169]
      s.barrierReg s.barrierOffset none .tile (some (.reg s.policyReg))⟩ := by
  fin_cases i
  · exact Flow.code_693
  · exact Flow.code_700
  · exact Flow.code_719
  · exact Flow.code_727
  · exact Flow.code_745
  · exact Flow.code_753
  · exact Flow.code_771
  · exact Flow.code_779
  · exact Flow.code_1163
  · exact Flow.code_1173
  · exact Flow.code_1191
  · exact Flow.code_1200
  · exact Flow.code_1376
  · exact Flow.code_1383

private theorem inputIssueSites :
    OpPcsFast kernel.code tensorOp (List.ofFn (fun i : Fin 14 => (inputSite i).pc)) = true := by
  decide +kernel

/-- An actual tensor load is one of the decoded Q or Bias sites. -/
theorem actualInputIssuePc {l : Launch} {m : Mem0} {A : List Assumption} {X : Execution}
    (hX : Consistent l kernel A m X) {i : EvId} {pc addr : Nat} {spec : TensorCopy.Spec}
    (he : X.get i = some ⟨pc, .tensorIssue addr spec⟩) : ∃ j : Fin 14, pc = (inputSite j).pc := by
  rcases get_source hX he with ⟨_, hBad⟩ | ⟨_, ins, _, _, hc, hf⟩
  · cases hBad
  have hOp : tensorOp ins.op = true := by
    cases h : tensorOp ins.op
    · exact (fires_notTensor (eventTmpl_notTensor h) hf addr spec rfl).elim
    · rfl
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp (OpPcsFast.mem inputIssueSites hc hOp)
  exact ⟨j, hj.symm⟩

private theorem inputSiteAddresses (i : Fin 14) :
    174 ≤ (inputSite i).pc ∧ (inputSite i).pc < 1901 ∧
      (inputSite i).sharedOffset ≤ 216064 ∧ (inputSite i).sharedOffset % 128 = 0 ∧
      (inputSite i).barrierOffset % 8 = 0 := by
  fin_cases i <;> decide

/-- The ABI parameter object chooses Q or Bias independently of the box coordinates. -/
def inputParam (site : InputSite) : Nat := if site.bias then 11 else 9

def inputMapAddress (p : Params) (site : InputSite) : Nat :=
  if site.bias then p.biasMapAddress else p.qMapAddress

def inputMap (p : Params) (site : InputSite) : TensorDescriptor.Descriptor 2 :=
  if site.bias then p.biasMap else p.qMap

/-- The exact instruction operands that determine the input box's launch descriptor and origin. -/
def inputSiteFacts (l : Launch) (site : InputSite)
    (col row head barrier policy : Nat) : List (Nat × Value) :=
  [(2535, b32 l.sharedBase), (site.mapReg, .ptr 64 true (.param (param (inputParam site))) 0),
    (site.colReg, b32 col), (site.rowReg, b32 row), (7169, b32 head),
    (site.barrierReg, b32 barrier), (site.policyReg, b64 policy)]

def inputSiteSpec (p : Params) (l : Launch) (g : Nat) (site : InputSite)
    (col row head barrier : Nat) : TensorCopy.Spec :=
  let dst : Loc := ⟨.shared, g / l.block, l.sharedBase + site.sharedOffset⟩
  let mbar : Loc := ⟨.shared, g / l.block, barrier + site.barrierOffset⟩
  ⟨⟨2, inputMap p site, inputCoordinate col row head, dst, none⟩, mbar, false, .one⟩

variable {p : Params} {l : Launch}

private theorem inputMapBinding {m : Mem0} (hp : Pre p l m) (s : InputSite) :
    l.paramObjects (param (inputParam s)) = some (mapParam (inputParam s), inputMapAddress p s) ∧
    inputMapAddress p s % 64 = 0 ∧ inputMapAddress p s + 128 ≤ 2 ^ 64 ∧
    l.tensorMaps (inputMapAddress p s) = some ⟨2, inputMap p s⟩ ∧
    TensorDescriptor.Valid (inputMap p s) := by
  have hQ := hp.maps 9 p.qMapAddress ⟨2, p.qMap⟩ (by simp)
  have hBias := hp.maps 11 p.biasMapAddress ⟨2, p.biasMap⟩ (by simp)
  cases h : s.bias
  · simp only [inputParam, inputMapAddress, inputMap, h, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hQ.1, hQ.2.1, hQ.2.2.1, hQ.2.2.2.1, hQ.2.2.2.2.1⟩
  · simp only [inputParam, inputMapAddress, inputMap, h, ↓reduceIte]
    exact ⟨hBias.1, hBias.2.1, hBias.2.2.1, hBias.2.2.2.1, hBias.2.2.2.2.1⟩

/-- The converted ABI parameter pointer resolves to its launch descriptor. -/
theorem inputMapReady {m : Mem0} (hp : Pre p l m) {g : Nat} {t : TState} {s : InputSite}
    (hReg : t.regs s.mapReg = some (.ptr 64 true (.param (param (inputParam s))) 0)) :
    tensorMap l g t (.reg s.mapReg) [.reg s.colReg, .reg s.rowReg, .reg 7169] .tile =
      .ok (inputMapAddress p s, ⟨2, inputMap p s⟩) := by
  obtain ⟨hObj, hAlign, hRange, hMap, hValid⟩ := inputMapBinding hp s
  have hAddr : tensorMapAddress l g t (.reg s.mapReg) = .ok (inputMapAddress p s) := by
    have hCheck : inputMapAddress p s ≤ 18446744073709551488 := by omega
    simp [tensorMapAddress, readValue, readReg, hReg, hObj, mapParam, ParamObjectDecl.bytes,
      hAlign, hCheck, bind, Except.bind, pure, Except.pure]
  simp [tensorMap, hAddr, hAlign, hMap, hValid, TensorMode.coordinates,
    bind, Except.bind, pure, Except.pure]

private theorem inputOrigin (col row head : Nat)
    (hc : col < 2 ^ 31) (hr : row < 2 ^ 31) (hh : head < 2 ^ 31) :
    (fun i : Fin 3 => (BitVec.ofNat 32
      ([BitVec.ofNat 64 col, BitVec.ofNat 64 row, BitVec.ofNat 64 head].getD i.val 0).toNat
      ).toInt) = inputCoordinate col row head := by
  funext i
  have hWord {n : Nat} (hn : n < 2 ^ 31) :
      (BitVec.ofNat 32 (BitVec.ofNat 64 n).toNat).toInt = n := by
    rw [toNat_ofNat_lt (show n < 2 ^ 64 by omega)]
    exact toInt_ofNat_lt32 hn
  fin_cases i
  · exact hWord hc
  · exact hWord hr
  · exact hWord hh

/-- The selected loader operands resolve the descriptor and exact box of its tensor issue. -/
theorem loaderInputOut {m : Mem0} (hp : Pre p l m) (i : Fin 14)
    {g col row head barrier policy : Nat} (hg : g < l.threads) (hc : col < 2 ^ 31)
    (hr : row < 2 ^ 31) (hh : head < 2 ^ 31) (hBar : barrier + (inputSite i).barrierOffset < 2 ^ 32)
    (hBarAlign : barrier % 8 = 0) (hPolicy : policy < 2 ^ 64)
    (hBox : TensorDescriptor.BoxAligned (inputMap p (inputSite i)) (inputCoordinate col row head))
    {t : TState}
    (ht : At t (inputSite i).pc (inputSiteFacts l (inputSite i) col row head barrier policy)) :
    out kernel Assumptions.all l g t = .ev (.tensorIssue (inputMapAddress p (inputSite i))
      (inputSiteSpec p l g (inputSite i) col row head barrier) (next t)) := by
  let s := inputSite i
  let addr := inputMapAddress p s
  let spec := inputSiteSpec p l g s col row head barrier
  obtain ⟨hLo, hHi, hShared, hA128, hA8⟩ := inputSiteAddresses i
  have hMap := inputMapReady hp (g := g) ht.2.2.2.2.2.1
  have hSh := hp.shared.2.1
  have hBound : l.sharedBase + s.sharedOffset < 2 ^ 32 := by
    change s.sharedOffset ≤ 216064 at hShared
    omega
  have hD : sharedEffAddr l g t false 2535 s.sharedOffset =
      .ok ⟨.shared, g / l.block, l.sharedBase + s.sharedOffset⟩ :=
    effAddr_b32_off ht.2.2.2.2.1 hBound
  have hDAlign : (l.sharedBase + s.sharedOffset) % 128 = 0 := by
    have hb := hp.shared.1
    change s.sharedOffset % 128 = 0 at hA128
    omega
  have hM : mbarLoc l g t s.barrierReg s.barrierOffset =
      .ok ⟨.shared, g / l.block, barrier + s.barrierOffset⟩ := by
    have hal : (barrier + s.barrierOffset) % 8 = 0 := by
      change s.barrierOffset % 8 = 0 at hA8
      omega
    unfold mbarLoc
    rw [effAddr_b32_off ht.2.2.2.2.2.2.2.2.2.1 hBar]
    simp [s, hal, bind, Except.bind, pure, Except.pure]
  have hCol := readBits_b32 (L := l) (g := g) ht.2.2.2.2.2.2.1
    (show col < 2 ^ 32 by omega)
  have hRow := readBits_b32 (L := l) (g := g) ht.2.2.2.2.2.2.2.1
    (show row < 2 ^ 32 by omega)
  have hHead := readBits_b32 (L := l) (g := g) ht.2.2.2.2.2.2.2.2.1
    (show head < 2 ^ 32 by omega)
  have hCs : [.reg s.colReg, .reg s.rowReg, .reg 7169].mapM (readBits l g t 32) =
      .ok [BitVec.ofNat 64 col, BitVec.ofNat 64 row, BitVec.ofNat 64 head] := by
    simp [s, List.mapM_cons, List.mapM_nil, hCol, hRow, hHead, bind, Except.bind,
      pure, Except.pure]
  have hAlign := (requireBoxAligned_eq_ok (inputMap p s) (inputCoordinate col row head)).mpr hBox
  have hLoad : tensorLoadCopy l g t false false 2535 s.sharedOffset (.reg s.mapReg)
      [.reg s.colReg, .reg s.rowReg, .reg 7169] s.barrierReg s.barrierOffset .tile =
        .ok (addr, spec) := by
    dsimp [s] at hD hM hCs hDAlign hAlign ⊢
    simp only [tensorLoadCopy, hMap, hD, bind, Except.bind, pure, Except.pure]
    simp only [hDAlign, Bool.false_eq_true, ↓reduceIte, hM, hCs,
      TensorMode.transfer, TensorMode.rowCoordinates]
    rw [inputOrigin col row head hc hr hh, hAlign]
    rfl
  have hPolicyRead : cachePolicyRead l g t (some (.reg s.policyReg)) = .ok () := by
    have hReg : t.regs s.policyReg = some (b64 policy) := ht.2.2.2.2.2.2.2.2.2.2.1
    simp only [cachePolicyRead, readBits_b64 hReg hPolicy, bind, Except.bind, pure, Except.pure]
  have hCta : g / l.block < l.grid := (Nat.div_lt_iff_lt_mul (by rw [hp.block]; decide)).2 hg
  have hCl : CtaInCluster l (g / l.block) (g / l.block) := ⟨hCta, hCta, rfl⟩
  have hGrid : l.clusterGridValid := hp.launch.1
  have hRoute : TensorRoute l (g / l.block) spec.clusterAddress spec.group spec.sharedBase
      spec.mbar :=
    ⟨hGrid, rfl, rfl, hCl, hCl, fun _ => ⟨rfl, rfl⟩,
      (sameCtaGroup_iff l .one _ _).2 ⟨hCl, rfl⟩⟩
  have hCode : kernel.code[t.pc]? = some ⟨none, .cpTensor false false 2535 s.sharedOffset
      (.reg s.mapReg) [.reg s.colReg, .reg s.rowReg, .reg 7169] s.barrierReg
      s.barrierOffset none .tile (some (.reg s.policyReg))⟩ := by
    rw [ht.1]
    exact inputSiteCode i
  change out kernel Assumptions.all l g t = .ev (.tensorIssue addr spec (next t))
  rw [loaderOutCore (by rw [ht.1]; exact hLo) (by rw [ht.1]; omega),
    out_event ht.2.2.2.1 hCode rfl rfl]
  change Out.ev (tensorTmpl l g t (.cpTensor false false 2535 s.sharedOffset (.reg s.mapReg)
    [.reg s.colReg, .reg s.rowReg, .reg 7169] s.barrierReg s.barrierOffset none .tile
    (some (.reg s.policyReg)))) = _
  simp [tensorTmpl, hPolicyRead, hLoad, hRoute, bind, Except.bind, pure, Except.pure, ofExec]

/-- At a reached input checkpoint, a maximal trace records the decoded tensor load issue. -/
theorem loaderInputOfMaximal {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (i : Fin 14)
    {g pos col row head barrier policy : Nat} (hg : g < l.threads) (hc : col < 2^31)
    (hr : row < 2^31) (hh : head < 2^31) (hBar : barrier+(inputSite i).barrierOffset < 2^32)
    (hBarAlign : barrier%8 = 0) (hPolicy : policy < 2^64)
    (hBox : TensorDescriptor.BoxAligned (inputMap p (inputSite i)) (inputCoordinate col row head))
    {t u : TState} {ending : Option TState}
    (hu : At u (inputSite i).pc (inputSiteFacts l (inputSite i) col row head barrier policy))
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t))
    (hTail : Run kernel Assumptions.all l g t ((X.tr g).drop pos) ending)
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u) (hPos : 0 < pos)
    (hBound : pos ≤ (X.tr g).length) (hRelease : pos = (X.tr g).length → Step.Released l X g) :
    X.get (g,pos) = some ⟨(inputSite i).pc,.tensorIssue (inputMapAddress p (inputSite i))
      (inputSiteSpec p l g (inputSite i) col row head barrier)⟩ ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (pos+1)) (some (next u)) ∧
      Run kernel Assumptions.all l g (next u) ((X.tr g).drop (pos+1)) ending := by
  let addr := inputMapAddress p (inputSite i)
  let spec := inputSiteSpec p l g (inputSite i) col row head barrier
  have hn : Next kernel Assumptions.all l g t u (.tensorIssue addr spec (next u)) :=
    ⟨hLocal,loaderInputOut hp i hg hc hr hh hBar hBarAlign hPolicy hBox hu⟩
  obtain ⟨he,hPast,hRest⟩ := Step.deferred_copy_issue_of_maximal hMax hg hn
    (fun _ _ => Iff.rfl) (.inr ⟨addr,spec,rfl⟩) hPrefix hTail hPos hBound hRelease
    (Assumptions.wfStep.quiet hMax.1 le_snoc rfl (Execution.noNewRead_snoc rfl))
  exact ⟨hu.1 ▸ he,hPast,hRest⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
