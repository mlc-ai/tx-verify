-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvWBase
public import Kernels.InklingRelDecode.Proof.Launch
public import Lemmas.Flow.Fire
public import Lemmas.Flow.NotShfl
public import Lemmas.Flow.TcMmaTs

@[expose] public section

/-!
# Tools of the event shapes: tensor core commits and MMAs

The generic steps behind the shapes of the MMA warp, each stated on the registers its
instruction reads:

* `resolve_unit`: a `tcgen05.commit.cta_group::1` of a thread that is alone in its cluster
  (`UnitCta`, which `Pre` gives) resolves to `commitSpec` (group one, cluster base the CTA itself,
  cluster size one);
* `fires_qk_event`, `fires_pv_event`: a `tcgen05.mma.cta_group::1.kind::f16` of the kernel's two
  forms (A and B in shared memory; A in Tensor Memory, B in shared memory) issues the event of
  the Core's decoding of its instruction descriptor and of its shared-memory descriptors (the
  operand specification of `TcMma.makeOperands`), with the destination column, the accumulate flag
  and the four zero lane masks its operands read.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.EvW
open PTX PTX.Flow PTX.Proof

noncomputable section
set_option maxRecDepth 100000

variable {A : List Assumption} {L : Launch} {g : Nat} {t u : TState} {pc : Nat} {e : Event}
  {Q : Params} {mem0 : Mem0}

/-- The thread's CTA is the only CTA of its cluster. -/
structure UnitCta (L : Launch) (g : Nat) : Prop where
  grid : L.clusterGridValid
  places : ∀ k, (L.clusterPlaces k).shape = ⟨1, 1, 1⟩
  cta : g / L.block < L.grid
  nclusters : L.nclusters = L.grid

theorem unitCta_of_pre (hpre : Pre Q L mem0) (hg : g < L.threads) : UnitCta L g where
  grid := hpre.launchValid.1
  places := clusterPlaces_unit hpre
  cta := by
    have hblock : 0 < L.block := by rw [hpre.block]; omega
    rw [Launch.threads] at hg
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg)
  nclusters := hpre.nclusters

/-- The thread is its own cluster's CTA of rank zero, so `cta_group::1` instructions address
its own CTA. -/
theorem peer_self (hu : UnitCta L g) :
    L.peerCta (g / L.block) (L.rankOfCta (g / L.block)) = some (g / L.block) := by
  have hc : g / L.block < L.nclusters := by rw [hu.nclusters]; exact hu.cta
  rw [Launch.rankOfCta_unit hu.places hc]
  exact Launch.peerCta_unit hu.places hc hu.cta

/-- The commit specification of a thread whose cluster is its own CTA, for the barrier `m`. -/
def commitSpec (cta : Nat) (m : Loc) : TcCommit.Spec := ⟨.one, m, 1, cta, 1⟩

theorem resolve_unit (hu : UnitCta L g) (a : Nat) :
    TcCommit.resolve L .one (g / L.block) ⟨.shared, g / L.block, a⟩
      (BitVec.ofNat 16 (2 ^ L.rankOfCta (g / L.block))) =
      some (commitSpec (g / L.block) ⟨.shared, g / L.block, a⟩) := by
  have hc : g / L.block < L.nclusters := by rw [hu.nclusters]; exact hu.cta
  have h1 := Launch.rankOfCta_unit hu.places hc
  have h2 := Launch.clusterOfCta_unit hu.places hc
  have h3 := Launch.clusterStart_unit hu.places (g / L.block)
  have h4 := Launch.clusterSizeOf_unit hu.places (g / L.block)
  unfold TcCommit.resolve
  simp only [h1, h2, h3, h4, commitSpec]
  simp [hu.grid, hu.cta]

theorem operands_unit (hone : L.peerCta (g / L.block) (L.rankOfCta (g / L.block)) =
    some (g / L.block)) (dsc : TcMma.Descriptor) (da db : TcShared.Descriptor)
    (hd : dsc.group = .one) :
    TcMma.makeOperands L (g / L.block) dsc da db =
      some ⟨dsc, da, db, g / L.block, g / L.block, none, {}⟩ := by
  rw [TcMma.makeOperands, hd, Launch.ctaGroup_one, hone]
  rfl

/-- **A QK MMA issue.** -/
theorem fires_qk_event (hone : L.peerCta (g / L.block) (L.rankOfCta (g / L.block)) =
    some (g / L.block)) (hg : g < L.threads)
    {dst ra rb ri c la lb : Nat} {en : Opnd} {acc : Bool}
    (hd : t.regs dst = some (b32 c)) (hc : c < 2 ^ 32)
    (hA : t.regs ra = some (Mma.desc la)) (hla : la < 2 ^ 31) (hla' : la / 2 ^ 15 % 2 = 0)
    (hB : t.regs rb = some (Mma.desc lb)) (hlb : lb < 2 ^ 31) (hlb' : lb / 2 ^ 15 % 2 = 0)
    (hI : t.regs ri = some (b32 Mma.qkIdesc)) (he : mmaEnable t en = .ok acc)
    (hf : Fires pc (eventTmpl Loader.asms L g t (.tcMma (.dense .one false .f16 dst
      (.smem (.reg ra)) (.reg rb) (.reg ri) Mma.masks0 en))) e (some u)) :
    ∃ da db dsc, TcMma.decode .one false .f16 Mma.qkIdesc = some dsc ∧
      TcShared.decode (la + Mma.descHi * 2 ^ 32) = some da ∧
      TcShared.decode (lb + Mma.descHi * 2 ^ 32) = some db ∧
      e = ⟨pc, .tc (.mma c ⟨dsc, da, db, g / L.block, g / L.block, none, {}⟩ acc
        [0, 0, 0, 0])⟩ := by
  obtain ⟨da, hda⟩ := Mma.desc_decode hla hla'
  obtain ⟨db, hdb⟩ := Mma.desc_decode hlb hlb'
  obtain ⟨dsc, hdi, hgr⟩ : ∃ dsc, TcMma.decode .one false .f16 Mma.qkIdesc = some dsc ∧
      dsc.group = .one := ⟨_, rfl, rfl⟩
  have hs := operands_unit hone dsc da db hgr
  have ht := tc_mma_en (L := L) (mask := Mma.masks0) (ms := [0, 0, 0, 0]) hg hd hc
    hA (by unfold Mma.descHi; omega) hB (by unfold Mma.descHi; omega) hI (by decide) rfl
    rfl he hda hdb hdi hs
  simp only [eventTmpl] at hf
  rw [ht] at hf
  exact ⟨da, db, dsc, hdi, hda, hdb, hf.1⟩

/-- **A PV MMA issue**: A from Tensor Memory at `[a + aoff]`. -/
theorem fires_pv_event (hone : L.peerCta (g / L.block) (L.rankOfCta (g / L.block)) =
    some (g / L.block)) (hg : g < L.threads)
    {dst ta rb ri c a lb : Nat} {aoff : Int} (haoff : 0 ≤ aoff) {en : Opnd} {acc : Bool}
    (hd : t.regs dst = some (b32 c)) (hc : c < 2 ^ 32)
    (hA : t.regs ta = some (b32 a)) (ha : a < 2 ^ 32)
    (hB : t.regs rb = some (Mma.vdesc lb)) (hlb : lb < 2 ^ 15)
    (hI : t.regs ri = some (b32 Mma.pvIdesc)) (he : mmaEnable t en = .ok acc)
    (hf : Fires pc (eventTmpl Loader.asms L g t (.tcMma (.dense .one false .f16 dst
      (.tmem ta aoff) (.reg rb) (.reg ri) Mma.masks0 en))) e (some u)) :
    ∃ db dsc, TcMma.decode .one false .f16 Mma.pvIdesc = some dsc ∧
      TcShared.decode (lb + 2 ^ 26 + Mma.descHi * 2 ^ 32) = some db ∧
      e = ⟨pc, .tc (.mma c ⟨dsc, db, db, g / L.block, g / L.block, some (a + aoff.toNat), {}⟩
        acc [0, 0, 0, 0])⟩ := by
  obtain ⟨db, hdb⟩ := Mma.vdesc_decode hlb
  obtain ⟨dsc, hdi, hgr, htr⟩ : ∃ dsc, TcMma.decode .one false .f16 Mma.pvIdesc = some dsc ∧
      dsc.group = .one ∧ dsc.transposeA = false := ⟨_, rfl, rfl, rfl⟩
  have hs := operands_unit hone dsc db db hgr
  rcases hoff : tmemOffset a aoff with f | a'
  · exfalso
    have hr : (TcMmaInstr.dense .one false .f16 dst (.tmem ta aoff) (.reg rb) (.reg ri)
        Mma.masks0 en).rule = some .threadTc := rfl
    have hmt : mmaTmpl L g t (.dense .one false .f16 dst (.tmem ta aoff) (.reg rb) (.reg ri)
        Mma.masks0 en) = mmaTmemTmpl L g t .one false .f16 dst ta aoff (.reg rb) (.reg ri)
        Mma.masks0 en none {} := by
      simp only [mmaTmpl, hr]
      rfl
    simp only [eventTmpl, tcTmpl, hmt, mmaTmemTmpl, readBits_b32 hd hc, readBits_b32 hA ha, bind,
      Except.bind, hoff, Proof.toNat_ofNat_lt (show a < 2 ^ 64 by omega)] at hf
    simp [ofExec, hg, Fires] at hf
  · have ht := tc_mmaTs (L := L) (mask := Mma.masks0) (ms := [0, 0, 0, 0]) hg hd hc hA ha hoff
      (b := lb + 2 ^ 26 + Mma.descHi * 2 ^ 32) hB (by unfold Mma.descHi; omega) hI (by decide)
      rfl rfl he hdb hdi htr hs
    simp only [eventTmpl] at hf
    rw [ht] at hf
    refine ⟨db, dsc, hdi, hdb, ?_⟩
    rw [hf.1]
    have h1 : a' = a + aoff.toNat := by
      unfold tmemOffset at hoff
      dsimp only at hoff
      split_ifs at hoff with hcol
      · simp only [pure, Except.pure, Except.ok.injEq] at hoff
        subst hoff
        omega
    subst h1
    rfl

end
end PTX.Kernels.InklingRelDecode.Proof.EvW
