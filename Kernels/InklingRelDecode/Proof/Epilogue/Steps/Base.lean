-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Control.Machine
public import Kernels.InklingRelDecode.Proof.Lib.ControlSpan
public import Kernels.InklingRelDecode.Proof.Lib.CtlSteps
public import Lemmas.Flow.Step.SiteCases
public import Lemmas.Flow.LandsU

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue.Control
open PTX PTX.Flow PTX.Proof

variable {e : Entry} {L : Launch} {g : Nat} {v : Value}

theorem straight {s z : Site} {gd op} (fetch : kernel.code[s.pc]? = some ⟨gd,op⟩)
    (locality : op.isLocal=false)
    (guardAt : Inv e (g%L.block) ⟨s,v⟩ → Code.GuardTrue (facts e L g v s.pc) gd)
    (fire : ∀ {t ev u}, t.sub=0 → Fires s.pc (eventTmpl Assumptions.all L g t op) ev (some u) →
      u=PTX.next t)
    (go : ∀ ev, next e L g ⟨s,v⟩ ev = some (some ⟨z,v⟩))
    (ok : Inv e (g%L.block) ⟨s,v⟩ → Inv e (g%L.block) ⟨z,v⟩)
    (seg : SegU kernel Assumptions.all L g (s.pc+1) (facts e L g v s.pc)
      z.pc (facts e L g v z.pc)) : (code e L g).StepAtU ⟨s,v⟩ where
  site := fun h => ⟨_,fetch,locality,guardAt h⟩
  step := by
    intro t ev u ins ht hi hc hf
    obtain rfl := Option.some.inj (hc.symm.trans fetch)
    obtain rfl := fire ht.2.1 hf
    obtain ⟨t',steps,good⟩ := Code.landsU (C := code e L g) (d := ⟨z,v⟩)
      (At.next (Code.at_of_atD ht rfl rfl)) seg (ok hi) rfl rfl
    exact .inl (.inr ⟨_,_,go ev,steps,good⟩)

theorem first_inv (e : Entry) (t : Nat) (v : Value) : Inv e t ⟨firstStore e.valid (lead t),v⟩ := by
  unfold firstStore; split_ifs <;> trivial

theorem store_inv {e : Entry} {t : Nat} (v : Value) (h : e.valid=true) (n : Nat) :
    Inv e t ⟨storeAt n,v⟩ := by
  unfold storeAt; split <;> first | exact h | trivial

end PTX.Kernels.InklingRelDecode.Proof.Epilogue.Control
