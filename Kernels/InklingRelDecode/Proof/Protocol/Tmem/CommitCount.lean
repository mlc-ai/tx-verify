-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarCommits
import Kernels.InklingRelDecode.Proof.Mma.Export.ScoreCredit
import Kernels.InklingRelDecode.Proof.Lib.IssueCount

@[expose] public section

/-! # The commits before a score commit

The score commit of block `b` is preceded by at most `b / 2` commits to the slot of its parity:
the blocks of one slot commit once each, in order. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar
open PTX PTX.Flow PTX.MbarRing

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **At most `b / 2` score commits of the slot precede the commit of block `b`.** -/
public theorem commits_before_commit (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) (rows : MbarRows Q L X)
    (words : RoleBytes L X) {c s y k sp b} (hy : y < L.threads) (warp : y%L.block/32 = 7)
    (he : X.get (y,k) = some ⟨2499,.tc (.commit sp)⟩)
    (hb : pollRound 2462 ((X.tr y).take k) = b+1) (slot : s.val = b%2) :
    ((X.tr y).take k).countP (commitsTo ((Object.score s).loc L c)) ≤ b/2 := by
  apply Lib.count_le_tags (fun j => (pollRound 2462 (((X.tr y).take k).take j) - 1)/2)
  · intro j e atJ kind
    obtain ⟨ji,atJ'⟩ := take_event atJ
    obtain ⟨sp1,get1,s1⟩ := score_receipt hp hX hf rows hy atJ' kind
    obtain ⟨pos,-,-⟩ := Mma.Export.score_polls hp hX hf warp get1
    have mono := countP_take_mono (okPollAt 2462) (X.tr y) ji.le
    rw [List.take_take,Nat.min_eq_left ji.le]
    change pollRound 2462 _ ≤ pollRound 2462 _ at mono
    by_contra hne
    have heq : pollRound 2462 ((X.tr y).take j) = b + 1 := by omega
    exact absurd (Mma.Export.score_unique hp hX hf words warp get1 he (by omega)) (by omega)
  · intro j j' e f ekh ek ejh ej eq
    obtain ⟨ji,ek'⟩ := take_event ekh
    obtain ⟨ji',ej'⟩ := take_event ejh
    obtain ⟨sp1,get1,s1⟩ := score_receipt hp hX hf rows hy ek' ek
    obtain ⟨sp2,get2,s2⟩ := score_receipt hp hX hf rows hy ej' ej
    obtain ⟨p1,-,-⟩ := Mma.Export.score_polls hp hX hf warp get1
    obtain ⟨p2,-,-⟩ := Mma.Export.score_polls hp hX hf warp get2
    rw [List.take_take,List.take_take,Nat.min_eq_left ji.le,Nat.min_eq_left ji'.le] at eq
    exact Mma.Export.score_unique hp hX hf words warp get1 get2 (by omega)

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar
