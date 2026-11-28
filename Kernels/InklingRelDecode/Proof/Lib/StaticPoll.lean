-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Flow.WaitLoopPcs
import Lemmas.Flow.NotBulk
import Lemmas.Flow.NotWait

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow

def pollSites : List Nat := [1257,2239,2374,2462,2510,2565]

private theorem sites : OpPcsFast kernel.code pollOp pollSites = true := by decide +kernel

private def spin (K : Kernel) (pc : Nat) : Bool :=
  (K.spinExit? pc).isSome && (K.pollDst pc).any K.spinPred

private theorem spins : pollSites.all (spin kernel) = true := by decide +kernel

private theorem canonical {K : Kernel} {pc : Nat} (hx : spin K pc = true) :
    ∃ exit, K.CanonicalSpin pc exit := by
  unfold spin at hx
  cases he : K.spinExit? pc with
  | none => simp only [he,Option.isSome_none,Bool.false_and,Bool.false_eq_true] at hx
  | some ex =>
    cases hd : K.pollDst pc with
    | none => simp only [hd,Option.any_none,Bool.and_false,Bool.false_eq_true] at hx
    | some p =>
      simp only [he,hd,Option.isSome_some,Option.any_some,Bool.true_and] at hx
      exact ⟨ex,he,p,hd,hx⟩

theorem poll_site {L A m X i pc l q ok acq sc} (hX : Consistent L kernel A m X)
    (he : X.get i = some ⟨pc,.wait l q ok acq sc⟩) :
    pc ∈ pollSites ∧ ∃ exit, kernel.CanonicalSpin pc exit := by
  obtain ⟨_,bad⟩ | ⟨_,ins,_,_,hc,hf⟩ := get_source hX he
  · cases bad
  by_cases h : ∃ p b o x a s, ins.op = .mbarWait p b o x a s
  · obtain ⟨p,b,o,x,a,s,hop⟩ := h
    have hpc := OpPcsFast.mem sites hc (by rw [hop]; rfl)
    exact ⟨hpc,canonical (List.all_eq_true.mp spins pc hpc)⟩
  · push Not at h
    exact absurd rfl (fires_notWait (eventTmpl_notWait h) hf l q ok acq sc)

end PTX.Kernels.InklingRelDecode.Proof.Lib
