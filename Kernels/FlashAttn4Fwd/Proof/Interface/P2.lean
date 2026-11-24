-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Interface.Score
public import Lemmas.Order.WarpBarOrdinal

@[expose] public section

/-! # What the thread layer exports for the second P-ready objects

Stage `st`'s second P-ready object of a pair (`pReady2Bar`, offset `160 + 8 st` of the leader CTA,
count 8) publishes the columns `112 …` of `P`. In score tile `u` (`sPolls = u + 1`) each softmax
thread of the stage stores those columns (`tcgen05.st`), waits for its stores
(`tcgen05.wait::st`), passes the warp's `bar.warp.sync -1` of the tile (its `u`-th: one per tile),
then elects (`elect.sync -1`), and the elected lane arrives on the object of the pair's leader
(one release arrival at cluster scope, its `u`-th on the object). The 4 warps of the stage in the
2 CTAs of the pair make the 8 arrivals of a phase. The leader's MMA warp polls the object, with
the parity of its earlier successful polls.

The fields are event-level facts of single threads, from the run invariants of the softmax
(`Softmax.Counts`: the tile's warp barrier, election and arrival) and of the MMA warp
(`Mma.Counts`: its polls), and the commit targets and copy barriers of the kernel's sites. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow TcMma

noncomputable section

/-- The member mask of every lane (`-1` as a 32-bit operand). -/
def fullMask : Nat := 4294967295

/-- The full mask names every lane. -/
theorem electMember_full {lane : Nat} (h : lane < 32) : electMember fullMask lane := by
  refine ⟨h, ?_⟩
  rw [show fullMask = 2 ^ 32 - 1 by rfl, Nat.testBit_two_pow_sub_one]
  simpa using h

/-- The thread layer's facts for the second P-ready objects. -/
structure P2Facts (L : Launch) (X : Execution) : Prop where
  /-- An arrival on stage `st`'s second P-ready object of CTA `c` in tile `u` is a softmax
  thread's of the stage, of the pair led by `c`: one release unit at cluster scope without
  transaction bytes, its `u`-th arrival on the object, after the tile's warp barrier (`u + 1`
  before it) and after an election of all lanes that returned its lane. -/
  p2_arrive : ∀ {g k pc tx cnt c st : Nat} {rel : Bool} {sc : MbarScope}, g < L.threads →
    st < 2 → X.get (g, k) = some ⟨pc, .arrive (pReady2Bar L c st) tx cnt rel sc⟩ →
      leadCta (ctaOf L g) = c ∧ warpOf L g < 8 ∧ warpOf L g / 4 = st ∧
        tx = 0 ∧ cnt = 1 ∧ rel = true ∧ sc = .cluster ∧
        arrivals (pReady2Bar L c st) ((X.tr g).take k) + 1 = sPolls L X g st k ∧
        warpBars X g k = sPolls L X g st k ∧
        ∃ e pce inst, e < k ∧ X.get (g, e) = some ⟨pce, .elect fullMask inst (laneOf L g)⟩
  /-- A poll of stage `st`'s second P-ready object of CTA `c` is a thread's of warp 12 of `c`,
  with the parity of its earlier successful polls of the object; a successful one acquires at
  cluster scope. -/
  p2_poll : ∀ {g i pc p c st : Nat} {ok acq : Bool} {sc : MbarScope}, g < L.threads → st < 2 →
    X.get (g, i) = some ⟨pc, .wait (pReady2Bar L c st) p ok acq sc⟩ →
      ctaOf L g = c ∧ warpOf L g = 12 ∧
        p % 2 = okPolls (pReady2Bar L c st) ((X.tr g).take i) % 2 ∧
        (ok = true → acq = true ∧ sc = .cluster)
  /-- No tensor copy completes on a second P-ready object. -/
  p2_tensor : ∀ {i : EvId} {pc a c st : Nat} {sp : TensorCopy.Spec}, st < 2 →
    X.get i = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar ≠ pReady2Bar L c st
  /-- No commit arrives on a second P-ready object. -/
  p2_commit : ∀ {i : EvId} {pc c st : Nat} {sp : TcCommit.Spec} {rank : Fin 16}, st < 2 →
    X.get i = some ⟨pc, .tc (.commit sp)⟩ → TcCommit.target sp rank ≠ some (pReady2Bar L c st)
  /-- A softmax thread's warp barriers name every lane. -/
  soft_warpBar : ∀ {h j m inst : Nat}, h < L.threads → warpOf L h < 8 →
    X.WarpBar (h, j) m inst → m = fullMask

end
end PTX.Kernels.FlashAttn4Fwd.Proof
