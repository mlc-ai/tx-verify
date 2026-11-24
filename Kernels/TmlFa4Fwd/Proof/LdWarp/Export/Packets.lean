-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.Mem
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Fits
import Kernels.TmlFa4Fwd.Proof.LdWarp.Open
import Kernels.TmlFa4Fwd.Proof.LdWarp.Page
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.CpCount
import Kernels.TmlFa4Fwd.Proof.Startup.Export.Mem
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The packet of a row copy is one of the tile's -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Loader

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

/-- The commits before a packet of a block, from the block's rounds. -/
private theorem rounds_lt {o : Option Blk} {ib nc : Nat} {v : V}
    (hm1 : sv (Epilogue.addi v.su.r28 (-1)) = sv v.su.r28 - 1) (hib : ib ≤ 1)
    (hRd : RoundsB o ib v nc) (ho : o ≠ none) (h6 : o ≠ some .tma6) :
    ((nc : Nat) : Int) + 1 ≤ max (2 * sv v.su.r28) 2 := by
  rcases o with _ | (_ | _ | _ | _)
  · exact (ho rfl).elim
  · have h : nc = ib := hRd
    omega
  · obtain ⟨r, -, h2, hlt, hnc⟩ := hRd
    unfold wRn at hlt
    omega
  · obtain ⟨r, -, hle, hlt, hnc⟩ := hRd
    have hw0 : w0 v.su.r28 = wRn v.su.r28 := by
      unfold w0
      rw [ite_eq_right (by omega)]
    rw [hw0] at hnc
    omega
  · exact (h6 rfl).elim

/-- **The packet of a row copy** is below twice the tile's blocks, and below two. -/
theorem ld_pkt_lt (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) {pc : Nat}
    {sp : AsyncCopy.Spec} (he : X.get (g, k) = some ⟨pc, .copy sp⟩) :
    ∃ R bal, Epilogue.Picked p L g R bal ∧
      ((pkt X g k : Nat) : Int) + 1 ≤ max (2 * sv (r28Ref p L g R bal)) 2 := by
  have hg := Frame.lt_of_get hX he
  have hub : ∀ f, (⟨pc, .copy sp⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  rcases LdWarp.open_ev hp hX hFw hw he hub with ⟨s', n', -, -, -, hi, hev'⟩ |
    ⟨b, d, n, hσ, h0, hR, -, hev⟩
  · exact (start_mem hev' hi.2 trivial).elim
  obtain ⟨a1, -, -, -⟩ := Loader.copy_site hev hub
  have hcpsite : d.site.isCp = true := by rw [← a1]; rfl
  obtain ⟨per, v, i, j, hs⟩ : ∃ per v i j, d.site = .cp per v i j := by
    revert hcpsite
    cases d.site <;> simp [Loader.Site.isCp]
  have hF : LFits p L g d (n .shfl) (n .vote) (n (.load .commit)) := (hR.2 h0).2
  have hb : d.site.blk = true := by rw [hs]; cases per <;> rfl
  obtain ⟨-, -, ⟨R, bal, hP, hr28⟩, ⟨-, hRd⟩, ⟨⟨v₀, hsu, -⟩, -⟩⟩ := lfits_blk_of hb hF
  have hpk : pkt X g k = n (.load .commit) := by
    rw [← (ld_cp hp hX hFw hw he).commits, ← count hσ]
    refine List.countP_congr fun e _ => ?_
    obtain ⟨pce, kd⟩ := e
    cases kd <;> simp [isAsyncCommit, cls, Loader.cls]
  have hge : -2 ^ 24 ≤ sv d.v.su.r28 := by rw [hsu]; exact r28_ge v₀
  have hm1 := sv_addi_neg1 d.v.su.r28 (by omega)
  refine ⟨R, bal, hP, ?_⟩
  rw [← hr28, hpk]
  rw [hs] at hRd
  have hib : inBlk (.cp per v i j) ≤ 1 := by simp only [inBlk]; split <;> omega
  exact rounds_lt hm1 hib hRd (by cases per <;> simp [bc]) (by cases per <;> simp [bc])

end
end PTX.Kernels.TmlFa4Fwd.Proof
