-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TensorLoad
public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Lemmas.Flow.TensorLoadFacts

@[expose] public section

/-! # A tensor load whose operands pass the checks is no undefined behaviour

-- domain: consistent

`tensorLoadCopy_of`: the copy of a unicast tensor load from the results of its operand checks
(map, destination, barrier, coordinates, box alignment); `route_self`: a CTA's own shared words
are routed in a launch of one-CTA clusters; `tensor_nonub`: with them the issue event is no
fault. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- **The copy of a tensor load from its operand checks.** -/
theorem tensorLoadCopy_of {t : TState} {ca gt : Bool} {dst mb : Nat} {off moff : Int}
    {map : Opnd} {cs : List Opnd} {lm : TensorMode} {a outer : Nat}
    {d : TensorDescriptor.Descriptor outer} {dl ml : Loc} {vs : List (BitVec 64)}
    (hmap : tensorMap L g t map cs lm = .ok (a, ⟨outer, d⟩))
    (hdst : sharedEffAddr L g t ca dst off = .ok dl) (h128 : dl.addr % 128 = 0)
    (hmb : (if ca then mbarClusterLoc L g t mb moff else mbarLoc L g t mb moff) = .ok ml)
    (hvs : cs.mapM (readBits L g t 32) = .ok vs)
    (hba : TensorDescriptor.BoxAligned (lm.transfer d)
      (fun axis : Fin (outer + 1) => (BitVec.ofNat 32 (vs.getD axis.val 0).toNat).toInt)) :
    tensorLoadCopy L g t ca gt dst off map cs mb moff lm = .ok (a,
      ⟨⟨outer, lm.transfer d,
        fun axis : Fin (outer + 1) => (BitVec.ofNat 32 (vs.getD axis.val 0).toNat).toInt, dl,
        lm.rowCoordinates fun j : Fin 4 => (BitVec.ofNat 32 (vs.getD (j.val + 1) 0).toNat).toInt⟩,
        ml, ca, if gt then CtaGroup.two else CtaGroup.one⟩) := by
  unfold tensorLoadCopy
  cases ca <;>
    simp only [Bool.false_eq_true, ↓reduceIte] at hmb hdst ⊢ <;>
    simp only [bind, Except.bind, pure, Except.pure, hmap, hdst, h128, hmb, hvs, ↓reduceIte,
      requireBoxAligned, hba]

/-- A CTA's own shared words are routed in a launch of one-CTA clusters. -/
theorem route_self (hp : Pre P L m) {c a b : Nat} {ca : Bool} (hc : c < L.grid) :
    TensorRoute L c ca .one ⟨.shared, c, a⟩ ⟨.shared, c, b⟩ := by
  refine ⟨hp.launchValid.1, rfl, rfl, ⟨hc, hc, rfl⟩, ⟨hc, hc, rfl⟩, fun _ => ⟨rfl, rfl⟩,
    ⟨⟨hc, hc, rfl⟩, ?_⟩⟩
  simp [Launch.ctaGroupRanks, CtaGroup.size]

/-- **A unicast tensor load that passes its checks is no fault.** -/
theorem tensor_nonub {A : List Assumption} {t : TState} {ca gt : Bool} {dst mb : Nat}
    {off moff : Int} {map : Opnd} {cs : List Opnd} {lm : TensorMode} {pol : Option Opnd}
    {pc : Nat} {e : Event} {o : Option TState} {a : Nat} {s : TensorCopy.Spec}
    (hpol : cachePolicyRead L g t pol = .ok ())
    (hc : tensorLoadCopy L g t ca gt dst off map cs mb moff lm = .ok (a, s))
    (hr : TensorRoute L (g / L.block) s.clusterAddress s.group s.sharedBase s.mbar)
    (hf : Fires pc (eventTmpl A L g t (.cpTensor ca gt dst off map cs mb moff none lm pol)) e o) :
    ∀ f, e.kind ≠ .ub f := by
  have hf' : Fires pc (tensorTmpl L g t (.cpTensor ca gt dst off map cs mb moff none lm pol)) e
      o := hf
  simp only [tensorTmpl, ofExec, bind, Except.bind, pure, Except.pure, hpol, hc, hr,
    ↓reduceIte, Fires] at hf'
  rw [hf'.1]
  intro f h
  cases h

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
