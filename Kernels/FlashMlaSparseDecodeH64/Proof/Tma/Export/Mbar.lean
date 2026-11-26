-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Tma
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaLen
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.ObjCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.RefStep

@[expose] public section

/-! # The TMA lane's mbarrier row

`mbarRow_tma`: an event of a warp-5 lane at a pc of the TMA code that names an mbarrier is fired
from a TMA state (`tma_at`, `Common/Where.lean`) whose site is one of the role's mbarrier sites,
on the site's object (`Tma/Objs.lean`, `Tma/ObjCnt.lean`); the reference invariant's counts are
the lane's prefix counts of successful polls and arrivals (`lane5_okPolls`, `lane5_arrivals`,
`Common/TmaLane.lean`), which give the ring slots and parities of `TmaUse`: block `r` polls and
arrives on slot `r % 4` of the coordinate ring and `r % 2` of the raw tile. A gather moves 2304
bytes (`tma_gather_bytes`, `Common/TmaLen.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The ring's parity word reads as its parity. -/
private theorem prW_W {q : Nat} (hq : q < 2) :
    (truncBits 32 (Arith32.andi (Arith32.zext16 (Arith32.W q)) 255)).toNat % 2 = q := by
  interval_cases q <;> decide

/-- The tile's flipped parity word reads as the flipped parity. -/
private theorem pfW_W {q : Nat} (hq : q < 2) :
    (truncBits 32 (Arith32.andi (Arith32.zext16w (Arith32.xor16 (Arith32.W q))) 255)).toNat % 2 =
      (q + 1) % 2 := by
  interval_cases q <;> decide

/-- **Row `MbarRow.Tma`**: every event of a warp-5 lane at a pc of the TMA code that names an
mbarrier is one of `TmaUse`. -/
theorem mbarRow_tma (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : MbarRow.Tma P L X := by
  intro g k e l _ he hat hm
  have hub : ∀ f, e.kind ≠ .ub f := by
    intro f hk
    obtain ⟨pc, kd⟩ := e
    simp only at hk
    subst hk
    simp [Frame.MbarOf] at hm
  obtain ⟨hw, hr⟩ := hat
  obtain ⟨d, hR, -, hev, hl, -⟩ := tma_at hp hX hFw he hub hr
  have hc := hR (lane5_take_noUb hX he)
  have hP := lane5_okPolls hp hX hFw hw k
  have hA := lane5_arrivals hp hX hFw hw k
  obtain ⟨hpc, hk⟩ := hev
  obtain ⟨pc, kd⟩ := e
  simp only at hpc hk hub ⊢
  subst hpc
  tma_state d
  cases s with
  | qWait =>
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · subst hk
      simp only [Frame.MbarOf] at hm
      have hl' := hm.trans (Tma.qUtW_loc hp)
      refine .qWait rfl hl' ⟨ok, by rw [hm]; rfl⟩ ?_
      rw [hP, (Tma.core_pro ⟨rfl, by simp, by simp⟩).mp hc _ (by simp), hl']
      exact Tma.tcnt_pro0 hp
    · exact absurd hk (hub f)
  | storeWait =>
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · subst hk
      simp only [Frame.MbarOf] at hm
      have hl' := hm.trans (Tma.lastW_loc hp)
      refine .lastWait rfl hl' ⟨ok, by rw [hm]; rfl⟩ ?_
      rw [hP, (Tma.core_pro ⟨rfl, by simp, by simp⟩).mp hc _ (by simp), hl']
      exact Tma.tcnt_pro1 hp
    · exact absurd hk (hub f)
  | coordWait =>
    obtain ⟨⟨-, -, -, -, -, -, hslot, -, hpr, -⟩, hn⟩ := (Tma.core_loop rfl).mp hc
    simp only at hslot hpr hn
    subst hpr
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · subst hk
      simp only [Frame.MbarOf] at hm
      have hl' : l = loc L g (.coordReady (slot4 cnt.toNat)) :=
        hm.trans ((Tma.ready_of hslot).trans (Tma.ready_loc hp (slot4 cnt.toNat)))
      have h4 : polls4 L g .coordReady ((X.tr g).take k) = cnt.toNat := by
        unfold polls4
        rw [hP, hP, hP, hP, hn _ (by simp), hn _ (by simp), hn _ (by simp), hn _ (by simp),
          Tma.tcnt_ready hp _ _ _ _ 0, Tma.tcnt_ready hp _ _ _ _ 1,
          Tma.tcnt_ready hp _ _ _ _ 2, Tma.tcnt_ready hp _ _ _ _ 3]
        simp [Tma.useAt, Tma.ind, ringUses, Tma.Site.stage]
        omega
      have h1 : okPolls l ((X.tr g).take k) = cnt.toNat / 4 := by
        rw [hP, hn _ (by simp), hl', Tma.tcnt_ready hp _ _ _ _ _]
        simp [Tma.useAt, Tma.ind, ringUses, Tma.Site.stage, slot4]
        omega
      refine .coordWait rfl (by rw [h4]; exact hl') ⟨ok, ?_⟩
      rw [h1, ← hm]
      exact congrArg (fun q => Kind.wait _ q ok true .cta) (prW_W (Nat.mod_lt _ (by decide)))
    · exact absurd hk (hub f)
  | rawWait =>
    obtain ⟨⟨-, -, -, -, -, hbuf, -, hpf, -, -⟩, hn⟩ := (Tma.core_loop rfl).mp hc
    simp only at hbuf hpf hn
    subst hpf
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · subst hk
      simp only [Frame.MbarOf] at hm
      have hl' : l = loc L g (.rawFree (slot2 cnt.toNat)) :=
        hm.trans ((Tma.free_of hbuf).trans (Tma.free_loc hp (slot2 cnt.toNat)))
      have h2 : polls2 L g .rawFree ((X.tr g).take k) = cnt.toNat := by
        unfold polls2
        rw [hP, hP, hn _ (by simp), hn _ (by simp), Tma.tcnt_free hp _ _ _ _ 0,
          Tma.tcnt_free hp _ _ _ _ 1]
        simp [Tma.useAt, Tma.ind, ringUses, Tma.Site.stage]
        omega
      have h1 : okPolls l ((X.tr g).take k) = cnt.toNat / 2 := by
        rw [hP, hn _ (by simp), hl', Tma.tcnt_free hp _ _ _ _ _]
        simp [Tma.useAt, Tma.ind, ringUses, Tma.Site.stage, slot2]
        omega
      refine .freeWait rfl (by rw [h2]; exact hl') ⟨ok, ?_⟩
      rw [h1, ← hm]
      exact congrArg (fun q => Kind.wait _ q ok true .cta)
        ((pfW_W (Nat.mod_lt (cnt.toNat / 2) (by decide))).trans (by omega))
    · exact absurd hk (hub f)
  | gather i =>
    obtain ⟨⟨-, -, -, -, -, hbuf, -, -, -, -⟩, hn⟩ := (Tma.core_loop rfl).mp hc
    simp only at hbuf hn
    rcases hk with ⟨a, s, hk, hmb⟩ | ⟨f, hk⟩
    · subst hk
      simp only [Frame.MbarOf] at hm
      have hl' : l = loc L g (.rawReady (slot2 cnt.toNat)) := by
        rw [← hm, hmb]
        exact (Tma.raw_of hbuf).trans (Tma.raw_loc hp (slot2 cnt.toNat))
      have h2 : arrs2 L g .rawReady ((X.tr g).take k) = cnt.toNat := by
        unfold arrs2
        rw [hA, hA, hn _ (by simp), hn _ (by simp), Tma.tcnt_raw hp _ _ _ _ 0,
          Tma.tcnt_raw hp _ _ _ _ 1]
        simp [Tma.useAt, Tma.ind, ringUses, Tma.Site.stage]
        omega
      have hpcR : 2165 < (Tma.Site.gather i).pc ∧ (Tma.Site.gather i).pc < 2332 :=
        (by decide : ∀ i : Fin 16, 2165 < (Tma.Site.gather i).pc ∧ (Tma.Site.gather i).pc < 2332) i
      exact .rawLoad ((by decide : ∀ i : Fin 16, (Tma.Site.gather i).pc ∈ rawLoadPcs) i)
        (by rw [h2]; exact hl')
        ⟨a, s, rfl, hm, tma_gather_bytes hp hX hFw he hpcR rfl⟩
    · exact absurd hk (hub f)
  | rawArrive =>
    obtain ⟨⟨-, -, -, -, -, hbuf, -, -, -, -⟩, hn⟩ := (Tma.core_loop rfl).mp hc
    simp only at hbuf hn
    simp only [Tma.EvK] at hk
    subst hk
    simp only [Frame.MbarOf] at hm
    have hl' : l = loc L g (.rawReady (slot2 cnt.toNat)) :=
      hm.trans ((Tma.raw_of hbuf).trans (Tma.raw_loc hp (slot2 cnt.toNat)))
    have h2 : arrs2 L g .rawReady ((X.tr g).take k) = cnt.toNat := by
      unfold arrs2
      rw [hA, hA, hn _ (by simp), hn _ (by simp), Tma.tcnt_raw hp _ _ _ _ 0,
          Tma.tcnt_raw hp _ _ _ _ 1]
      simp [Tma.useAt, Tma.ind, ringUses, Tma.Site.stage]
      omega
    exact .rawArrive rfl (by rw [h2]; exact hl') (by rw [hm]; rfl)
  | coordFree =>
    obtain ⟨⟨-, -, -, -, -, -, hslot, -, -, -⟩, hn⟩ := (Tma.core_loop rfl).mp hc
    simp only at hslot hn
    simp only [Tma.EvK] at hk
    subst hk
    simp only [Frame.MbarOf] at hm
    have hl' : l = loc L g (.coordFree (slot4 cnt.toNat)) :=
      hm.trans ((Tma.cfree_of hslot).trans (Tma.cfree_loc hp (slot4 cnt.toNat)))
    have h4 : arrs4 L g .coordFree ((X.tr g).take k) = cnt.toNat := by
      unfold arrs4
      rw [hA, hA, hA, hA, hn _ (by simp), hn _ (by simp), hn _ (by simp), hn _ (by simp),
        Tma.tcnt_cfree hp _ _ _ _ 0, Tma.tcnt_cfree hp _ _ _ _ 1,
        Tma.tcnt_cfree hp _ _ _ _ 2, Tma.tcnt_cfree hp _ _ _ _ 3]
      simp [ringUses]
      omega
    exact .coordFree rfl (by rw [h4]; exact hl') (by rw [hm]; rfl)
  | leave i => exact absurd rfl (hl i)
  | elect =>
    rcases hk with ⟨_, _, hk⟩ | ⟨f, hk⟩
    · subst hk; simp [Frame.MbarOf] at hm
    · exact absurd hk (hub f)
  | loadTopk | loadExtra =>
    rcases hk with ⟨_, _, hk⟩ | ⟨f, hk⟩
    · subst hk; simp [Frame.MbarOf] at hm
    · exact absurd hk (hub f)
  | coord0 _ | coord1 _ | coord2 _ | coord3 _ =>
    rcases hk with ⟨_, _, hk, -⟩ | ⟨f, hk⟩
    · subst hk; simp [Frame.MbarOf] at hm
    · exact absurd hk (hub f)
  | outBar | exit =>
    simp only [Tma.EvK] at hk
    subst hk
    simp [Frame.MbarOf] at hm

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
