-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Reuse

@[expose] public section

/-! # The order of a tensor load and an MMA read of one slot

A tensor load of slot `s` of production `n` (its loader's earlier issues there over three) is
visible to an MMA read of the slot by an MMA thread that has polled the slot's full barrier
`n + 1` times: the thread's `(n + 1)`-th successful poll observes the load's completion
(`PairTmaRing.copy_observed`), and the read follows the poll (`copy_before_read`). An MMA read of
slot `s`, with fewer than `n` commits of its thread to the slot up to it, is visible to a tensor
load of the slot of production `n`: the loader's last successful empty poll before the load
acquires a later commit of the MMA thread (`PairTmaRing.read_observed`), and the load follows
the poll (`read_before_copy`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow AsyncCopy MBarrier

noncomputable section

namespace InputRing

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A tensor load before an MMA read.** A tensor load of slot `s` of production `n` is ordered
before an MMA read, at a byte both cover, of an MMA thread of the slot that has polled the slot's
full barrier at least `n + 1` times before the read. -/
theorem copy_before_read (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {s : Fin 4} {b : Fin 2} {km : Nat}
    (hkm : km < (X.tr (consumerOf L X c s b)).length)
    {gl kl pcl al : Nat} {spl : TensorCopy.Spec}
    (hel : X.get (gl, kl) = some ⟨pcl, .tensorIssue al spl⟩) (hml : spl.mbar = (slot L c s).full 0)
    (hpolls : ((X.tr gl).take kl).countP (issuesTo ((slot L c s).full 0)) / 3 + 1 ≤
      okPolls ((slot L c s).full 0) ((X.tr (consumerOf L X c s b)).take km))
    {x y z : Nat} {l : Loc} {isB : Bool} {idx : Nat}
    (hca : AsyncCovers X (gl, kl) (.write (.load x y z)) l)
    (hcb : AsyncCovers X (consumerOf L X c s b, km) (.mmaRead isB idx) l) :
    AsyncBefore L X l ((gl, kl), .write (.load x y z))
      ((consumerOf L X c s b, km), .mmaRead isB idx) :=
  PairTmaRing.copy_before_read hX (hyp hpre hX ht c s) hkm hel hml hpolls hca hcb

/-- **An MMA read before a tensor load.** An MMA read of slot `s` is ordered before a tensor
load of the slot, at a byte both cover, when the MMA thread's commits to the slot's empty
barrier up to the read are two fewer than the loader's successful empty polls before the load. -/
theorem read_before_copy (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) {c : Nat} {s : Fin 4} {b : Fin 2} {km : Nat}
    (hR : X.TcAsync (consumerOf L X c s b, km))
    {gl kl pcl al : Nat} {spl : TensorCopy.Spec}
    (hel : X.get (gl, kl) = some ⟨pcl, .tensorIssue al spl⟩) (hml : spl.mbar = (slot L c s).full 0)
    (hcnt : ((X.tr (consumerOf L X c s b)).take (km + 1)).countP
        (commitsTo ((slot L c s).empty 0)) + 2 ≤
      okPolls ((slot L c s).empty ⟨gl / L.block % 2, Nat.mod_lt _ (by decide)⟩)
        ((X.tr gl).take kl))
    {x y z : Nat} {l : Loc} {isB : Bool} {idx : Nat}
    (hca : AsyncCovers X (consumerOf L X c s b, km) (.mmaRead isB idx) l)
    (hcb : AsyncCovers X (gl, kl) (.write (.load x y z)) l) :
    AsyncBefore L X l ((consumerOf L X c s b, km), .mmaRead isB idx)
      ((gl, kl), .write (.load x y z)) ∧
      ∃ w ws, AsyncObserved X (consumerOf L X c s b, km) .mmaDone w true ws := by
  obtain ⟨a, rfl, hcta, -⟩ := issue_producer hX ht hel hml
  have ha : (⟨producerOf L X c s a / L.block % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = a :=
    Fin.ext (by simp only; omega)
  rw [ha] at hcnt
  exact PairTmaRing.read_before_copy hX (hyp hpre hX ht c s) hR hel hcnt hca hcb

end InputRing

end
end PTX.Kernels.Fp16Gemm8192.Proof
