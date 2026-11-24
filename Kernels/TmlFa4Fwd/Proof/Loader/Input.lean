-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Flow.TensorLoadFacts

@[expose] public section

/-! # The loader's tensor copies, as data

The fourteen decoded Q and Bias copies (`inputSite`: copy `c` of TMA group `t` is site `2 t + c`),
the launch's map each reads (`inputMap`), and that a register holding the map's parameter pointer
resolves to it (`inputMapReady`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
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

/-- The ABI parameter object chooses Q or Bias independently of the box coordinates. -/
def inputParam (site : InputSite) : Nat := if site.bias then 11 else 9

def inputMapAddress (p : Params) (site : InputSite) : Nat :=
  if site.bias then p.biasMapAddress else p.qMapAddress

def inputMap (p : Params) (site : InputSite) : TensorDescriptor.Descriptor 2 :=
  if site.bias then p.biasMap else p.qMap

variable {p : Params} {l : Launch}

private theorem inputMapBinding {m : Mem0} (hp : Pre p l m) (s : InputSite) :
    l.paramObjects (param (inputParam s)) = some (mapParam (inputParam s), inputMapAddress p s) ∧
    inputMapAddress p s % 64 = 0 ∧ inputMapAddress p s + 128 ≤ 2 ^ 64 ∧
    l.tensorMaps (inputMapAddress p s) = some ⟨2, inputMap p s⟩ ∧
    TensorDescriptor.Valid (inputMap p s) := by
  obtain ⟨hQo, hQa, hQr, hQm, hQv, -⟩ := hp.maps 9 p.qMapAddress ⟨2, p.qMap⟩ (by simp)
  obtain ⟨hBo, hBa, hBr, hBm, hBv, -⟩ := hp.maps 11 p.biasMapAddress ⟨2, p.biasMap⟩ (by simp)
  cases h : s.bias
  · simp only [inputParam, inputMapAddress, inputMap, h, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hQo, hQa, hQr, hQm, hQv⟩
  · simp only [inputParam, inputMapAddress, inputMap, h, ↓reduceIte]
    exact ⟨hBo, hBa, hBr, hBm, hBv⟩

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

/-- Copy `c` of TMA group `t`. -/
def siteOf (t : Fin 7) (c : Fin 2) : Fin 14 := ⟨2 * t.val + c.val, by omega⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
