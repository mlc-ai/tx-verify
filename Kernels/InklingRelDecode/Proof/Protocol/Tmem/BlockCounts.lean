-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarCommits
import Kernels.InklingRelDecode.Proof.Mma.Export.ScoreCredit
import Kernels.InklingRelDecode.Proof.Mma.Export.DoneCredit
import Kernels.InklingRelDecode.Proof.Protocol.P.DoneBudget
import Kernels.InklingRelDecode.Proof.Lib.IssueCount

@[expose] public section

/-! # The commits before an MMA issue

A QK issue of block `b` is preceded by at most `b / 2` commits to the score slot of its parity, a PV
issue of block `b - 1` by at most `b - 1` done commits. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar
open PTX PTX.Flow PTX.MbarRing

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **At most `b / 2` score commits of the slot precede the QK issue of block `b`.** -/
public theorem qk_commits_before (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (words : RoleBytes L X)
    {c s y k pc dst sp' acc mask b}
    (hy : y < L.threads)
    (he : X.get (y,k) = some ⟨pc,.tc (.mma dst sp' acc mask)⟩)
    (qk : pc ∈ [2483,2486,2488,2490,2492,2494,2496,2498]) (warp : y%L.block/32 = 7)
    (hb : pollRound 2462 ((X.tr y).take k) = b+1) (slot : s.val = b%2) :
    ((X.tr y).take k).countP (commitsTo ((Object.score s).loc L c)) ≤ b/2 := by
  apply Lib.count_le_tags (fun j => (pollRound 2462 (((X.tr y).take k).take j) - 1)/2)
  · intro j e atJ kind
    obtain ⟨ji,atJ'⟩ := take_event atJ
    obtain ⟨sp,get,sl⟩ := score_receipt hp hX hf rows hy atJ' kind
    obtain ⟨pos,-,-⟩ := Mma.Export.score_polls hp hX hf warp get
    have lt := Mma.Export.score_commit_lt hp hX hf words warp get ji he qk
    rw [List.take_take,Nat.min_eq_left ji.le]
    omega
  · intro j j' e f ekh ek ejh ej eq
    obtain ⟨ji,ek'⟩ := take_event ekh
    obtain ⟨ji',ej'⟩ := take_event ejh
    obtain ⟨sp1,get1,s1⟩ := score_receipt hp hX hf rows hy ek' ek
    obtain ⟨sp2,get2,s2⟩ := score_receipt hp hX hf rows hy ej' ej
    obtain ⟨p1,-,-⟩ := Mma.Export.score_polls hp hX hf warp get1
    obtain ⟨p2,-,-⟩ := Mma.Export.score_polls hp hX hf warp get2
    rw [List.take_take,List.take_take,Nat.min_eq_left ji.le,Nat.min_eq_left ji'.le] at eq
    exact Mma.Export.score_unique hp hX hf words warp get1 get2 (by omega)

/-- **At most `b - 1` done commits precede the PV issue that follows `b` PV polls.** -/
public theorem pv_commits_before (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (words : RoleBytes L X)
    {c y k pc dst sp' acc mask b}
    (hy : y < L.threads) (he : X.get (y,k) = some ⟨pc,.tc (.mma dst sp' acc mask)⟩)
    (pv : pc ∈ [2530,2533,2535,2537,2539,2541,2543,2545]) (warp : y%L.block/32 = 7)
    (hb : pollRound 2510 ((X.tr y).take k) = b) :
    ((X.tr y).take k).countP (commitsTo (Object.done.loc L c)) ≤ b-1 := by
  apply Lib.count_le_tags (fun j => pollRound 2510 (((X.tr y).take k).take j) - 1)
  · intro j e atJ kind
    obtain ⟨ji,atJ'⟩ := take_event atJ
    obtain ⟨sp,get⟩ := P.done_receipt hp hX hf rows hy atJ' kind
    obtain ⟨pos,-⟩ := Mma.Export.done_shuffles hp hX hf warp get
    have lt := Mma.Export.done_commit_lt hp hX hf words warp get ji he pv
    rw [List.take_take,Nat.min_eq_left ji.le]
    omega
  · intro j j' e f ekh ek ejh ej eq
    obtain ⟨ji,ek'⟩ := take_event ekh
    obtain ⟨ji',ej'⟩ := take_event ejh
    obtain ⟨sp1,get1⟩ := P.done_receipt hp hX hf rows hy ek' ek
    obtain ⟨sp2,get2⟩ := P.done_receipt hp hX hf rows hy ej' ej
    obtain ⟨p1,-⟩ := Mma.Export.done_shuffles hp hX hf warp get1
    obtain ⟨p2,-⟩ := Mma.Export.done_shuffles hp hX hf warp get2
    rw [List.take_take,List.take_take,Nat.min_eq_left ji.le,Nat.min_eq_left ji'.le] at eq
    exact Mma.Export.done_unique hp hX hf words warp get1 get2 (by omega)

/-- **At most `(b - 1) / 2 + 1` score commits of the slot of parity `(b - 1) % 2` precede the PV
issue that follows at most `b + 1` ready polls.** -/
public theorem pv_scores_before (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (words : RoleBytes L X)
    {c s y k b} (hy : y < L.threads) (warp : y%L.block/32 = 7)
    (hb : pollRound 2462 ((X.tr y).take k) ≤ b+1) (slot : s.val = (b-1)%2) :
    ((X.tr y).take k).countP (commitsTo ((Object.score s).loc L c)) ≤ (b-1)/2+1 := by
  apply Lib.count_le_tags (fun j => (pollRound 2462 (((X.tr y).take k).take j) - 1)/2)
  · intro j e atJ kind
    obtain ⟨ji,atJ'⟩ := take_event atJ
    obtain ⟨sp,get,sl⟩ := score_receipt hp hX hf rows hy atJ' kind
    obtain ⟨pos,-,-⟩ := Mma.Export.score_polls hp hX hf warp get
    have mono := countP_take_mono (okPollAt 2462) (X.tr y) ji.le
    rw [List.take_take,Nat.min_eq_left ji.le]
    change pollRound 2462 _ ≤ pollRound 2462 _ at mono
    omega
  · intro j j' e f ekh ek ejh ej eq
    obtain ⟨ji,ek'⟩ := take_event ekh
    obtain ⟨ji',ej'⟩ := take_event ejh
    obtain ⟨sp1,get1,s1⟩ := score_receipt hp hX hf rows hy ek' ek
    obtain ⟨sp2,get2,s2⟩ := score_receipt hp hX hf rows hy ej' ej
    obtain ⟨p1,-,-⟩ := Mma.Export.score_polls hp hX hf warp get1
    obtain ⟨p2,-,-⟩ := Mma.Export.score_polls hp hX hf warp get2
    rw [List.take_take,List.take_take,Nat.min_eq_left ji.le,Nat.min_eq_left ji'.le] at eq
    have par : (pollRound 2462 ((X.tr y).take j) - 1)%2 =
        (pollRound 2462 ((X.tr y).take j') - 1)%2 := by omega
    exact Mma.Export.score_unique hp hX hf words warp get1 get2 (by omega)

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar
