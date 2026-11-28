-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Alpha.Agree
public import Kernels.InklingRelDecode.Proof.Lib.RoundWords
public import Lemmas.Flow.OutKinds
import Kernels.InklingRelDecode.Proof.Softmax.Export.SentWord
import Kernels.InklingRelDecode.Proof.Softmax.Export.AlphaOperand

/-! # The words a lane sends and receives at pc 1838 are numbers or `-inf`

A lane's sent word is a number or `-inf` (`sent_ni`); the word it received is the sent word of the
lane 16 away (`partner_1838`). So every word of `roundWords` is. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX PTX.Proof PTX.Flow Softmax.Export Softmax.Data

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Both words of a shuffle of pc 1838 are numbers or `-inf`**, when the score loads return
numbers. -/
public theorem shfl5_ni (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (hS : ∀ g k a vals sh, X.get (g, k) = some ⟨1265, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x) {g k : Nat} {mode b c sent recv ok}
    (lane : g % L.block < 128)
    (get : X.get (g, k) = some ⟨1838, .shfl mode sent b c recv ok⟩) :
    SK.ni.Has sent ∧ SK.ni.Has recv := by
  refine ⟨sent_ni hp hX hf (hS g) get, ?_⟩
  obtain ⟨rfl, rfl, rfl⟩ := shfl5_shape hp hX get
  obtain ⟨j, ok', got, -⟩ := partner_1838 hp hX hf get lane
  exact sent_ni hp hX hf (hS _) got

/-- **Every word of the rounds of a lane is a number or `-inf`.** -/
public theorem roundWords_ni (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X)
    (hS : ∀ g k a vals sh, X.get (g, k) = some ⟨1265, .tc (.ld a vals sh)⟩ →
      ∀ x ∈ vals, SK.fl.Has x) {g j : Nat} (lane : g % L.block < 128) :
    ∀ p ∈ roundWords X g j, SK.ni.Has p.1 ∧ SK.ni.Has p.2 := by
  intro p hp'
  obtain ⟨e, he, hw⟩ := List.mem_flatMap.mp hp'
  obtain ⟨i, hi, hie⟩ := List.getElem_of_mem he
  have get : X.get (g, i) = some e := by
    show (X.tr g)[i]? = some e
    rw [← hie, List.getElem_take]
    exact List.getElem?_eq_getElem _
  obtain ⟨pc, kind⟩ := e
  cases kind with
  | shfl mode sent b c recv ok =>
    by_cases h : pc = 1838
    · subst h
      simp only [wordOf, List.mem_singleton] at hw
      subst hw
      exact shfl5_ni hp hX hf hS lane get
    · simp [wordOf, h] at hw
  | _ => simp [wordOf] at hw

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
