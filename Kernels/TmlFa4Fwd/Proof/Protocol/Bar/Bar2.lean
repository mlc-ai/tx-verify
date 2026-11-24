-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.WarpIndex
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Correction.Shape
public import Kernels.TmlFa4Fwd.Proof.Top.Table
public import Lemmas.Protocol.NamedBarSources
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Count
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Match
import Kernels.TmlFa4Fwd.Proof.Top.JRView
import Kernels.TmlFa4Fwd.Proof.Top.JRStub
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Obj
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Barrier 2: the 416 threads of the softmax, correction and MMA warps

Barrier 2 orders the MMA warp's Tensor Memory allocation before the other roles' accesses (its
first rendezvous, `bar.sync 2, 416` at every participant's `bar1` site) and their accesses
before the deallocation (its second: the softmax and correction lanes' `bar.arrive 2, 416` at
`barEnd`, the MMA lanes' `bar.sync 2, 416` before the deallocation).

* `bar2_ev`: every barrier-2 event of the shape tables passes the count 416 and is of a lane of
  warps 0 to 12 (the softmax warps' and the correction warps' named barriers are 3 to 12, the
  startup's is 0, the output and loader warps make none);
* `srcs2`, `shape2`: barrier 2's sources and group, the hypotheses of the barrier hand-offs. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem corr_nbW_ne2 (k : Fin 2) : 2 ≠ (Correction.nbW L g k).toNat := by
  have h := corr_nb_range L g
  fin_cases k <;> simp only [Correction.nbW] <;> omega

/-- A role state's lane is in its role's warps: softmax 0 to 7. -/
theorem jr_soft {d : (frag p L g .softmax).D} {n : Cls → Nat}
    (hJ : JR p L g (.inr ⟨.softmax, d⟩, n)) : Prologue.warpIndex L g < 8 := by
  simp only [JR_eq] at hJ
  split_ifs at hJ with h8
  · exact h8
  · unfold RefAll at hJ
    split_ifs at hJ <;> simp_all [Mma.Ref, Epilogue.Ref, LdWarp.Ref, CorrWarp.Ref]

set_option maxHeartbeats 8000000 in
/-- **Every barrier-2 event of the shape tables** passes 416 threads, from a lane of warps 0 to
12. -/
theorem bar2_ev (hp : Pre p L m) {σ : (thread p L g).D} {e : Event} {cnt : Option Nat}
    {mode : BarMode} (hJ : JR p L g σ) (hi : (thread p L g).inv σ) (hev : TEv p L g σ e)
    (hk : e.kind = .bar 2 cnt mode) : cnt = some 416 ∧ Prologue.warpIndex L g < 13 := by
  have hw16 := Prologue.warpIndex_lt hp g
  obtain ⟨σ1, n⟩ := σ
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  have h1 : ∀ k, 2 ≠ (Correction.nbW L g k).toNat := fun k => corr_nbW_ne2 k
  have h4 : (2 : Nat) ≠ (if Softmax.stg L g = true then 12 else 11) := by split <;> decide
  rcases σ1 with s | ⟨i, d⟩
  · have := start_barOps hJ hev
    simp at this
  cases i with
  | epilogue => exact (epi_nobar hev 2 cnt mode rfl).elim
  | loader b => exact (ld_nobar hev).elim
  | stub r =>
    exact (jr_stub hJ).elim
  | mma =>
    rcases d with s | ⟨⟨⟩, d⟩
    · rcases hev with ⟨_, _, _, hk⟩ | ⟨_, _, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk
    · have h := mma_bar hev
      simp only [Prod.mk.injEq] at h
      exact ⟨h.2.1, by rw [jr_mma hJ]; omega⟩
  | correction =>
    have hw := jr_corr hJ hw16
    have hev := (hev.1.data_or_vote.resolve_right (by rintro ⟨_,_,hv⟩; cases hv))
    refine ⟨?_, by omega⟩
    unfold Correction.Ev at hev
    split at hev <;> first
      | exact (epi_nobar hev 2 cnt mode rfl).elim
      | exact (h1 _ (Kind.bar.inj hev).1).elim
      | (simp only [Kind.bar.injEq] at hev; exact hev.2.1.symm ▸ rfl)
      | (rcases hev with hev | ⟨_, hev⟩ <;> simp only [Kind.bar.injEq, reduceCtorEq] at hev;
          exact hev.2.1)
      | simp_all [Correction.rdOrUb]
  | softmax =>
    have h8 := jr_soft hJ
    have h3 : 2 ≠ (Softmax.nbW L g).toNat := by
      have := soft_nb_range (L := L) (g := g) (by simpa [Prologue.warpIndex] using h8)
      omega
    have hev := hev.1
    refine ⟨?_, by omega⟩
    unfold Softmax.Ev at hev
    split at hev <;> first
      | exact (epi_nobar hev 2 cnt mode rfl).elim
      | exact (h3 (Kind.bar.inj hev).1).elim
      | exact (h4 (Kind.bar.inj hev).1).elim
      | (simp only [Kind.bar.injEq] at hev; exact hev.2.1.symm ▸ rfl)
      | (rcases hev with hev | ⟨_, hev⟩ <;> simp only [Kind.bar.injEq, reduceCtorEq] at hev;
          exact hev.2.1)
      | simp_all [Softmax.rdOrUb, Softmax.tcLdOrUb]

section table
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
  (hT : (table p L).ShapeOkU (· < L.threads)) (hF : (table p L).Followed X (· < L.threads))
include hp hX hT hF

/-- **Barrier 2's arrivals**: every one is a lane of warps 0 to 12 passing 416 threads. -/
theorem srcs2 : NamedBar.Sources L X (some 416) (Finset.range 13) 2 := by
  rintro ⟨h, i⟩ pc cnt ⟨mode, he⟩ hh
  obtain ⟨σ, -, hJ, hi, hev⟩ := ev_at hp hX hT hF he (by intro f hf; cases hf)
  obtain ⟨hc, hw⟩ := bar2_ev hp hJ hi hev rfl
  exact ⟨by simpa [Prologue.warpIndex] using hw, hc⟩

end table

/-- Barrier 2's group: warps 0 to 12, 416 threads. -/
theorem shape2 (hp : Pre p L m) : NamedBar.Shape L (some 416) (Finset.range 13) 2 where
  pos := by simp
  target := by rw [hp.block]; rfl
  bound := by intro w hw; rw [hp.block]; simp at hw; omega
  id_lt := by decide

end
end PTX.Kernels.TmlFa4Fwd.Proof
