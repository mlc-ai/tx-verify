-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Mma
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.MmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Class
import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.LocCnt

@[expose] public section

/-! # The MMA lane's mbarrier row

`mbarRow_mma`: an event of a warp-4 lane at a pc of the MMA code that names an mbarrier is fired
from an MMA state (`mma_at`, `Common/Where.lean`) whose site is one of the role's mbarrier
sites, on the site's object (`Mma/Objs.lean`); the reference invariant's counts are the lane's
prefix counts of successful polls and commits (`lane4_okPolls`, `lane4_commits`,
`Common/MmaLane.lean`), which give the ring slots and parities of `MmaUse`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The block loop's parity word reads as its parity. -/
private theorem parW_W {q : Nat} (hq : q < 2) :
    (truncBits 32 (Mma.parW (Arith32.W q))).toNat % 2 = q := by
  interval_cases q <;> decide

/-- **Row `MbarRow.Mma`**: every event of a warp-4 lane at a pc of the MMA code that names an
mbarrier is one of `MmaUse`. -/
theorem mbarRow_mma (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : MbarRow.Mma P L X := by
  intro g k e l _ he hat hm
  have hub : ∀ f, e.kind ≠ .ub f := by
    intro f hk
    obtain ⟨pc, kd⟩ := e
    simp only at hk
    subst hk
    simp [Frame.MbarOf] at hm
  obtain ⟨hw, hr⟩ := hat
  obtain ⟨d, hR, hev, hl, -⟩ := mma_at hp hX hFw he hub hr
  have hc := hR (take_noUb hX he)
  have hP := lane4_okPolls hp hX hFw hw k
  have hC := lane4_commits hp hX hFw hw k
  obtain ⟨hpc, hk⟩ := hev
  obtain ⟨pc, kd⟩ := e
  simp only at hpc hk hub ⊢
  subst hpc
  obtain ⟨site, l0, l1, neg, cnt, pha, par⟩ := d
  cases site with
  | qLoad i =>
    rcases hk with ⟨a, s, hk, hmb, hby, -⟩ | ⟨f, hk⟩
    · subst hk
      simp only [Frame.MbarOf] at hm
      exact .qLoad (by fin_cases i <;> simp [Mma.Site.pc, qLoadPcs])
        (by rw [← hm, hmb, Mma.qTma_loc hp]) ⟨a, s, rfl, hm, hby⟩
    · exact absurd hk (hub f)
  | qArrive =>
    simp only [Mma.EvK] at hk
    subst hk
    simp only [Frame.MbarOf] at hm
    exact .qArrive rfl (hm.trans (Mma.qTma_loc hp)) (by rw [hm]; rfl)
  | qWait =>
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · subst hk
      simp only [Frame.MbarOf] at hm
      have hl' := hm.trans (Mma.qTma_loc hp)
      refine .qWait rfl hl' ⟨ok, by rw [hm]; rfl⟩ ?_
      rw [hP, (Mma.core_pro ⟨rfl, by simp, by simp⟩).mp hc _ (by simp), hl']
      exact Mma.cnt_pro0 hp
    · exact absurd hk (hub f)
  | qCopyWait =>
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · subst hk
      simp only [Frame.MbarOf] at hm
      have hl' := hm.trans (Mma.qUt_loc hp)
      refine .qCopyWait rfl hl' ⟨ok, by rw [hm]; rfl⟩ ?_
      rw [hP, (Mma.core_pro ⟨rfl, by simp, by simp⟩).mp hc _ (by simp), hl']
      exact Mma.cnt_pro1 hp
    · exact absurd hk (hub f)
  | qCopyCommit =>
    rcases hk with ⟨s, hk, hmb, hg, hself⟩ | ⟨f, hk⟩
    · subst hk
      obtain ⟨rank, ht⟩ := hm
      have hl' := hself rank l ht
      exact .qCommit rfl (hl'.trans (hmb.trans (Mma.qUt_loc hp))) ⟨s, rfl, hl'.symm, hg⟩
    · exact absurd hk (hub f)
  | kvWait =>
    obtain ⟨⟨-, -, -, -, -, hpha, hpar, -⟩, hn⟩ := (Mma.core_loop rfl).mp hc
    simp only at hpha hpar hn
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · subst hk
      simp only [Frame.MbarOf] at hm
      have h2 : polls2 L g .dequantReady ((X.tr g).take k) = cnt.toNat := by
        unfold polls2
        rw [hP, hP, hn _ (by simp), hn _ (by simp), Mma.cnt_ready hp _ _ 0,
          Mma.cnt_ready hp _ _ 1]
        simp [Mma.useAt, Mma.ind, ringUses, Mma.Site.idx]
        omega
      have hl' : l = loc L g (.dequantReady (slot2 cnt.toNat)) :=
        hm.trans (by rw [hpha]; exact Mma.ready_loc hp (slot2 cnt.toNat))
      have h1 : okPolls l ((X.tr g).take k) = cnt.toNat / 2 := by
        rw [hP, hn _ (by simp), hl', Mma.cnt_ready hp _ _ _]
        simp [Mma.useAt, Mma.ind, ringUses, Mma.Site.idx, slot2]
        omega
      refine .kvWait rfl (by rw [h2]; exact hl') ⟨ok, ?_⟩
      rw [h1, ← hm, hpar, parW_W (Nat.mod_lt _ (by decide))]
    · exact absurd hk (hub f)
  | soWait =>
    obtain ⟨⟨-, -, -, -, -, hpha, hpar, -⟩, hn⟩ := (Mma.core_loop rfl).mp hc
    simp only at hpha hpar hn
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · subst hk
      simp only [Frame.MbarOf] at hm
      have h2 : polls2 L g .soReady ((X.tr g).take k) = cnt.toNat := by
        unfold polls2
        rw [hP, hP, hn _ (by simp), hn _ (by simp), Mma.cnt_so hp _ _ 0,
          Mma.cnt_so hp _ _ 1]
        simp [Mma.useAt, Mma.ind, ringUses, Mma.Site.idx]
        omega
      have hl' : l = loc L g (.soReady (slot2 cnt.toNat)) :=
        hm.trans (by rw [hpha]; exact Mma.so_loc hp (slot2 cnt.toNat))
      have h1 : okPolls l ((X.tr g).take k) = cnt.toNat / 2 := by
        rw [hP, hn _ (by simp), hl', Mma.cnt_so hp _ _ _]
        simp [Mma.useAt, Mma.ind, ringUses, Mma.Site.idx, slot2]
        omega
      refine .soWait rfl (by rw [h2]; exact hl') ⟨ok, ?_⟩
      rw [h1, ← hm, hpar, parW_W (Nat.mod_lt _ (by decide))]
    · exact absurd hk (hub f)
  | qkCommit =>
    obtain ⟨-, hn⟩ := (Mma.core_loop rfl).mp hc
    obtain ⟨⟨-, -, -, -, -, hpha, -, -⟩, -⟩ := (Mma.core_loop rfl).mp hc
    simp only at hpha hn
    rcases hk with ⟨s, hk, hmb, hg, hself⟩ | ⟨f, hk⟩
    · subst hk
      obtain ⟨rank, ht⟩ := hm
      have hl' := hself rank l ht
      have h2 : cmts2 L g .qkDone ((X.tr g).take k) = cnt.toNat := by
        unfold cmts2
        rw [hC, hC, hn _ (by simp), hn _ (by simp), Mma.cnt_qk hp _ _ 0,
          Mma.cnt_qk hp _ _ 1]
        simp [Mma.useAt, Mma.ind, ringUses, Mma.Site.idx]
        omega
      refine .qkCommit rfl ?_ ⟨s, rfl, hl'.symm, hg⟩
      rw [h2, hl', hmb, hpha]
      exact Mma.qk_loc hp (slot2 cnt.toNat)
    · exact absurd hk (hub f)
  | pvCommit =>
    obtain ⟨-, hn⟩ := (Mma.core_loop rfl).mp hc
    obtain ⟨⟨-, -, -, -, -, hpha, -, -⟩, -⟩ := (Mma.core_loop rfl).mp hc
    simp only at hpha hn
    rcases hk with ⟨s, hk, hmb, hg, hself⟩ | ⟨f, hk⟩
    · subst hk
      obtain ⟨rank, ht⟩ := hm
      have hl' := hself rank l ht
      have h2 : cmts2 L g .svDone ((X.tr g).take k) = cnt.toNat := by
        unfold cmts2
        rw [hC, hC, hn _ (by simp), hn _ (by simp), Mma.cnt_sv hp _ _ 0,
          Mma.cnt_sv hp _ _ 1]
        simp [ringUses]
        omega
      refine .svCommit rfl ?_ ⟨s, rfl, hl'.symm, hg⟩
      rw [h2, hl', hmb, hpha]
      exact Mma.sv_loc hp (slot2 cnt.toNat)
    · exact absurd hk (hub f)
  | leave i => exact absurd rfl (hl i)
  | trap =>
    obtain ⟨f, hk⟩ := hk
    exact absurd hk (hub f)
  | elect =>
    rcases hk with ⟨_, _, hk⟩ | ⟨f, hk⟩
    · subst hk; simp [Frame.MbarOf] at hm
    · exact absurd hk (hub f)
  | loadTopk | loadExtra =>
    rcases hk with ⟨_, _, hk⟩ | ⟨f, hk⟩
    · subst hk; simp [Frame.MbarOf] at hm
    · exact absurd hk (hub f)
  | qCopy =>
    rcases hk with ⟨_, hk, -⟩ | ⟨f, hk⟩
    · subst hk; simp [Frame.MbarOf] at hm
    · exact absurd hk (hub f)
  | qk | pv =>
    rcases hk with ⟨_, hk, -⟩ | ⟨f, hk⟩
    · subst hk; simp [Frame.MbarOf] at hm
    · exact absurd hk (hub f)
  | qFence | qCopyFence | kvFence | soFence | outBar | exit =>
    simp only [Mma.EvK] at hk
    subst hk
    simp [Frame.MbarOf] at hm

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
