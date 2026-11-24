-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Epilogue.Barriers
public import Kernels.TmlFa4Fwd.Proof.OutputWritebackSpec
public import Kernels.TmlFa4Fwd.Proof.MbarAddressClosure

@[expose] public section

/-! # The output warp's barrier operands, for the upper layers

The statements the safety, protocol and progress layers consume, in the kernel's names
(`pollPc`, `freePc`, `readyLoc`, `writebackFreeLoc`), from the output warp's machine
(`Proof2.Epilogue.Barriers`). -/

namespace PTX.Kernels.TmlFa4Fwd.OutputWarp
open PTX PTX.Proof PTX.Flow Epilogue Prologue

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem wait_of_pc (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index pc : Nat} {target : Loc} {q : Nat} {ok acq : Bool} {scope : MbarScope}
    (he : X.get (g, index) = some ⟨pc, .wait target q ok acq scope⟩)
    (hSite : pc = 2958 ∨ pc = 2972) :
    ∃ st : Fin 2, pc = pollPc st ∧ target = readyLoc l g st ∧ q = 0 ∧ acq = true ∧
      scope = .cta := by
  obtain ⟨hw, hj5, -⟩ := Proof2.Epilogue.output_event (p := p) hp hX he
    (by simp only; omega) (by simp only; omega) (by rintro _ _ ⟨⟩)
  obtain ⟨st, hpc, ht, hq, ha, hs⟩ := Proof2.Epilogue.wait_site hp hX hw hj5 he
  refine ⟨st, ?_, ht, hq, ha, hs⟩
  rw [hpc]; fin_cases st <;> rfl

/-- The observed ready polls use parity zero and the matching output stage object. -/
theorem pollOperands (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index site : Nat} {target : Loc} {q : Nat} {ok acq : Bool} {scope : MbarScope}
    (he : X.get (g, index) = some ⟨site, .wait target q ok acq scope⟩)
    (hSite : site = 2958 ∨ site = 2972) :
    ∃ stage : Fin 2, site = pollPc stage ∧ target = readyLoc l g stage ∧
      q = 0 ∧ acq = true ∧ scope = .cta :=
  wait_of_pc hp hX he hSite

/-- Both actual output-ready polls use the stage objects at byte offsets 208 and 216. -/
theorem waitAddress (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index pc : Nat} {target : Loc} {q : Nat} {ok acq : Bool} {scope : MbarScope}
    (he : X.get (g, index) = some ⟨pc, .wait target q ok acq scope⟩)
    (hSite : pc = 2958 ∨ pc = 2972) :
    ∃ off ∈ [208, 216], target = ⟨.shared, g / l.block, l.sharedBase + off⟩ := by
  obtain ⟨st, -, rfl, -⟩ := wait_of_pc hp hX he hSite
  fin_cases st
  · exact ⟨208, by simp, rfl⟩
  · exact ⟨216, by simp, rfl⟩

/-- Both output-ready polls name initialized objects. -/
theorem waitInitObject (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index pc : Nat} {target : Loc} {q : Nat} {ok acq : Bool} {scope : MbarScope}
    (he : X.get (g, index) = some ⟨pc, .wait target q ok acq scope⟩)
    (hSite : pc = 2958 ∨ pc = 2972) :
    ∃ i : Fin 34, target = initObject l (g / l.block) i := by
  obtain ⟨off, hOff, rfl⟩ := waitAddress hp hX he hSite
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hOff
  rcases hOff with rfl | rfl <;>
    apply initObjectOfOffset <;> unfold initializedMbarOffset <;> decide

private theorem arrive_of_pc (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index pc : Nat} {target : Loc} {tx n : Nat} {rel : Bool} {scope : MbarScope}
    (he : X.get (g, index) = some ⟨pc, .arrive target tx n rel scope⟩)
    (hSite : pc = 2983 ∨ pc = 2985) :
    ∃ st : Fin 2, pc = freePc st ∧ target = writebackFreeLoc l g st ∧ tx = 0 ∧ n = 1 ∧
      rel = true ∧ scope = .cta := by
  obtain ⟨hw, hj5, -⟩ := Proof2.Epilogue.output_event (p := p) hp hX he
    (by simp only; omega) (by simp only; omega) (by rintro _ _ ⟨⟩)
  obtain ⟨-, -, -, st, -, hpc, ht, h1, h2, h3, h4⟩ := Proof2.Epilogue.arrive_site hp hX hw hj5 he
  refine ⟨st, ?_, ht, h1, h2, h3, h4⟩
  rw [hpc]; fin_cases st <;> rfl

private theorem freePc_cases (stage : Fin 2) : freePc stage = 2983 ∨ freePc stage = 2985 := by
  fin_cases stage <;> simp [freePc]

private theorem freePc_inj {st st' : Fin 2} (h : freePc st = freePc st') : st = st' := by
  fin_cases st <;> fin_cases st' <;> first | rfl | simp [freePc] at h

/-- An actual free event releases one lane on its own output stage. -/
theorem freeOperands (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {g index : Nat} {target : Loc} {tx n : Nat} {rel : Bool} {scope : MbarScope}
    (he : X.get (g, index) = some ⟨freePc stage, .arrive target tx n rel scope⟩) :
    target = writebackFreeLoc l g stage ∧ tx = 0 ∧ n = 1 ∧ rel = true ∧ scope = .cta := by
  obtain ⟨st, hpc, h⟩ := arrive_of_pc hp hX he (freePc_cases stage)
  obtain rfl := freePc_inj hpc
  exact h

/-- Both output-free arrivals name the stage objects at byte offsets 224 and 232. -/
theorem arriveAddress (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index pc : Nat} {target : Loc} {tx n : Nat} {rel : Bool} {scope : MbarScope}
    (he : X.get (g, index) = some ⟨pc, .arrive target tx n rel scope⟩)
    (hSite : pc = 2983 ∨ pc = 2985) :
    ∃ off ∈ [224, 232], target = ⟨.shared, g / l.block, l.sharedBase + off⟩ := by
  obtain ⟨st, -, rfl, -⟩ := arrive_of_pc hp hX he hSite
  fin_cases st
  · exact ⟨224, by simp, rfl⟩
  · exact ⟨232, by simp, rfl⟩

private theorem freePc_bounds (stage : Fin 2) : 2768 ≤ freePc stage ∧ freePc stage < 3099 := by
  fin_cases stage <;> decide

private theorem free_site {st stage : Fin 2}
    (h : (Proof2.Epilogue.Site.free st).pc = freePc stage) : st = stage := by
  fin_cases st <;> fin_cases stage <;> first | rfl | simp [Proof2.Epilogue.Site.pc, freePc] at h

/-- Every lane releases a given output stage at most once in its actual trace. -/
theorem freeIndexUnique (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {g i j : Nat} {target : Loc} {tx n : Nat} {rel : Bool} {scope : MbarScope}
    (hi : X.get (g, i) = some ⟨freePc stage, .arrive target tx n rel scope⟩)
    (hj : X.get (g, j) = some ⟨freePc stage, .arrive target tx n rel scope⟩) : i = j := by
  have hb := freePc_bounds stage
  obtain ⟨hw, hi5, -⟩ := Proof2.Epilogue.output_event (p := p) hp hX hi hb.1 hb.2
    (by rintro _ _ ⟨⟩)
  obtain ⟨-, hj5, -⟩ := Proof2.Epilogue.output_event (p := p) hp hX hj hb.1 hb.2
    (by rintro _ _ ⟨⟩)
  obtain ⟨di, ni, hσi, sti, hsi, hpci, -⟩ := Proof2.Epilogue.arrive_site hp hX hw hi5 hi
  obtain ⟨dj, nj, hσj, stj, hsj, hpcj, -⟩ := Proof2.Epilogue.arrive_site hp hX hw hj5 hj
  obtain rfl := free_site hpci.symm
  obtain rfl := free_site hpcj.symm
  rcases lt_trichotomy i j with h | h | h
  · exact (Proof2.Epilogue.free_unique hp hX hw h hσi hσj hsi hsj hi rfl).elim
  · exact h
  · exact (Proof2.Epilogue.free_unique hp hX hw h hσj hσi hsj hsi hj rfl).elim

/-- An output lane returns a stage's staging credit only after its ready acquire for that
stage. -/
theorem readyBeforeFree (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i : Nat} (stage : Fin 2) {target : Loc} {tx n : Nat} {rel : Bool} {scope : MbarScope}
    (he : X.get (g, i) = some ⟨freePc stage, .arrive target tx n rel scope⟩) :
    ∃ j < i, X.get (g, j) = some ⟨pollPc stage, .wait (readyLoc l g stage) 0 true true .cta⟩ := by
  have hb := freePc_bounds stage
  obtain ⟨hw, hi5, -⟩ := Proof2.Epilogue.output_event (p := p) hp hX he hb.1 hb.2
    (by rintro _ _ ⟨⟩)
  obtain ⟨d, n, hσ, st, hs, hpc, -⟩ := Proof2.Epilogue.arrive_site hp hX hw hi5 he
  obtain rfl := free_site hpc.symm
  obtain ⟨j, hji, hj5, pc', q, acq, sc, he'⟩ :=
    Proof2.Epilogue.ready_before_free hp hX hw hσ hs he
  obtain ⟨st', hpc', ht, rfl, rfl, rfl⟩ := Proof2.Epilogue.wait_site hp hX hw hj5 he'
  obtain rfl := Proof2.Epilogue.readyLoc_inj ht.symm
  refine ⟨j, hji, ?_⟩
  rw [he', hpc']
  fin_cases st' <;> rfl

end
end PTX.Kernels.TmlFa4Fwd.OutputWarp
