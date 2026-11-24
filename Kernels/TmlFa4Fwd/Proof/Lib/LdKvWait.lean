-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Fits
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Round
public import Kernels.TmlFa4Fwd.Proof.Mma.Export.Count
public import Kernels.TmlFa4Fwd.Proof.Progress.Time
public import Kernels.TmlFa4Fwd.Proof.Top.Table
import Kernels.TmlFa4Fwd.Proof.Common.View
import Kernels.TmlFa4Fwd.Proof.LdWarp.Page
import Kernels.TmlFa4Fwd.Proof.LdWarp.Pos
import Kernels.TmlFa4Fwd.Proof.LdWarp.Src
import Kernels.TmlFa4Fwd.Proof.Loader.Export.Parity
import Kernels.TmlFa4Fwd.Proof.Loader.Export.AcqRing
import Kernels.TmlFa4Fwd.Proof.Loader.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Loader.RefStepBlock
import Kernels.TmlFa4Fwd.Proof.Loader.RefStepTma
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.Lag
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.TileAgree
import Kernels.TmlFa4Fwd.Proof.Top.Register
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A loader lane at a wait for an empty K/V slot

`ld_kv_wait`: the wait of packet `i` (at a `slot` site the lane's packet, at the drain's `dw j` the
packet `j` past the tile's) polls slot `i % 3` with the parity of `i / 3 + 1`, after `i / 3`
successful polls; from packet 3 on the CTA's MMA rounds bound `i`, and the wait's time is at least
that of packet `i`'s slot. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- A loader state at a wait for an empty K/V slot. -/
def kvSite : Loader.Site → Bool
  | .slot _ _ | .dw _ => true
  | _ => false

theorem pkts_le (b : BitVec 64) (hb : -2 ^ 24 ≤ Loader.sv b) :
    (Loader.pkts b : Int) ≤ max (2 * Loader.sv b) 2 := by
  by_cases h : 2 ≤ Loader.sv b
  · have hs := sv_addm1 b h
    have hw : Loader.w0 b = Loader.wRn b := by simp only [Loader.w0]; split_ifs <;> omega
    simp only [Loader.pkts, hw, Loader.wRn, hs]
    push_cast
    omega
  · have h0 : Loader.w0 b = 0 := by simp only [Loader.w0]; split_ifs <;> omega
    have hs : Loader.sv (Flow.Arith32.addi b (-1)) = Loader.sv b - 1 := by
      simp only [Loader.sv, toSigned, Flow.Arith32.addm1_toNat] at h hb ⊢
      have h1 := Nat.mod_lt b.toNat (show 0 < 2 ^ 32 by norm_num)
      generalize b.toNat % 2 ^ 32 = a at *
      simp only [Nat.reduceSub, Nat.reducePow] at h hb ⊢
      split_ifs at h hb ⊢ <;> omega
    have hwr : Loader.wRn b = 0 := by
      simp only [Loader.wRn]
      rw [show Loader.sv (Epilogue.addi b (-1)) = Loader.sv b - 1 from hs]
      omega
    simp only [Loader.pkts, h0, hwr]
    rw [show Loader.sv (Epilogue.addi b (-1)) = Loader.sv b - 1 from hs]
    omega

/-- The packets of the tile of the MMA warp's rounds. -/
theorem pkts_rounds {R R' : Nat} {bal : BitVec 64} (hP : Epilogue.Picked p L g R' bal)
    (hR : MmaRounds p L g R) : Loader.pkts (Loader.r28Ref p L g R' bal) ≤ 2 * (R + 1) := by
  obtain ⟨r, b, hP', rfl⟩ := hR
  obtain ⟨rfl, rfl⟩ := hP.unique hP'
  have h := pkts_le (Loader.r28Ref p L g R' bal) (Loader.r28_ge _)
  have hsv : Loader.sv (Loader.r28Ref p L g R' bal) =
      Mma.Bs p L g (mmaRef p L g R' bal) := by
    rw [tile_agree (p := p) rfl R' bal]
    exact (toSigned_r32 _).symm
  rw [hsv] at h
  generalize Mma.Bs p L g (mmaRef p L g R' bal) = B at h ⊢
  omega

/-- What a wait for an empty K/V slot polls. -/
structure KvWait (p : Params) (L : Launch) (X : Execution) (g : Nat) (t i : Nat) : Prop where
  ok : okPolls (obj L g (56 + 8 * (i % 3))) (X.tr g) = i / 3
  late : 3 ≤ i → ∃ R, MmaRounds p L g R ∧ i < 2 * R + 5 ∧
    (Progress.doneBase p ≤ t ∨ i < 2 * R + 2 ∧
      Progress.clk p (Progress.slotOf p ((i - 2) / 2)) Progress.bandL ≤ t)

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hub : ¬ HasUb X) (hg : g < L.threads) {b : Bool} {d : Loader.D} {n : Cls → Nat}
  (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (.inr ⟨.loader b, d⟩, n)))
include hp hX hFw hub hg hσ

/-- **A loader lane at a wait for an empty K/V slot.** -/
theorem ld_kv_wait (hs : kvSite d.site = true) :
    (Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) ∧
    ∃ i, KvWait p L X g (Progress.time p L g (.inr ⟨.loader b, d⟩, n)) i ∧
      ∀ {pc q : Nat} {l : Loc} {ok acq : Bool} {sc : MbarScope},
        TEv p L g (.inr ⟨.loader b, d⟩, n) ⟨pc, .wait l q ok acq sc⟩ →
        l = obj L g (56 + 8 * (i % 3)) ∧ q % 2 = (i / 3 + 1) % 2 := by
  have hJ := (goodR hp hX hFw hg _).2 _ hσ
  obtain ⟨hw, hwb, hR⟩ := JR.loader hJ
  have hub0 : n .ub = 0 := by
    by_contra h
    obtain ⟨j, -, ⟨pc, kind⟩, hf, hk⟩ := exists_of_count hσ (Nat.pos_of_ne_zero h)
    cases kind <;> simp [cls] at hk
    exact hub ⟨(g, j), pc, _, hf⟩
  obtain ⟨hJl, hF⟩ := hR hub0
  obtain ⟨kk, A, hRing, hCnt⟩ := hJl.refE
  rw [← hwb] at hRing
  have hcm := hCnt.commit
  have hok : ∀ s : Fin 3, okPolls (obj L g (56 + 8 * s.val)) (X.tr g) =
      Loader.ringCnt (n (.load .commit) + Loader.acqOff d.site) s.val := by
    intro s
    have h1 := Loader.acq_ring hp hX hg hw hσ hub0 s
    simp only [LdWarp.lcn] at h1
    have h2 := count hσ (.load (.acquire (obj L g (56 + 8 * s.val))))
    rw [List.take_length] at h2
    exact h2.trans h1
  refine ⟨hw, ?_⟩
  cases hsite : d.site <;> rw [hsite] at hs <;> simp only [kvSite, Bool.false_eq_true] at hs
  case slot per vv =>
    simp only [LdWarp.lcn, hsite, Loader.arrAt, Loader.inPkt, Nat.add_zero] at hcm
    have hblk : d.site.blk = true := by rw [hsite]; cases per <;> rfl
    obtain ⟨-, -, hSu, hRd, -⟩ := Loader.lfits_blk_of hblk hF
    refine ⟨n (.load .commit), ⟨?_, fun h3 => ?_⟩, fun {pc q l ok acq sc} hev => ?_⟩
    · have := hok ⟨n (.load .commit) % 3, Nat.mod_lt _ (by decide)⟩
      rw [this, hsite]
      exact Loader.ringCnt_mod _
    · obtain ⟨R', bal, hP, hr⟩ := hSu
      have hR : MmaRounds p L g _ := ⟨R', bal, hP, rfl⟩
      have hlt : n (.load .commit) < Loader.pkts d.v.su.r28 := by
        refine Loader.nc_lt_pkts (s := .xl per vv 0) rfl ?_
        rw [hsite] at hRd
        cases per <;> cases vv <;> exact hRd
      rw [hr] at hlt
      have hle := pkts_rounds hP hR
      refine ⟨_, hR, by omega, .inr ⟨by omega, ?_⟩⟩
      have hper : per ≠ .prime := by
        rintro rfl
        rw [hsite] at hRd
        cases vv <;> simp [Loader.Rounds, Loader.bc, Loader.RoundsB, Loader.inBlk] at hRd <;> omega
      cases per
      · exact absurd rfl hper
      all_goals
        simp only [Progress.time, Progress.roleTime, Progress.Ld.time, hsite, Progress.Ld.slot,
          Progress.Ld.idx, Nat.sub_zero, Progress.clk]
        omega
    · cases ld_use (l := l) hp hRing hev rfl with
      | slot per' vv' ok' hs' hl hk =>
        rw [hsite] at hs'
        cases hs'
        refine ⟨by rw [hl, hcm], ?_⟩
        simp only [Kind.wait.injEq] at hk
        obtain ⟨-, rfl, -⟩ := hk
        obtain ⟨s, v, kk'⟩ := d
        simp only at hsite
        subst hsite
        rw [ldPar, Nat.mod_mod, Loader.slot_par hRing, hcm]
      | _ => simp_all
  case dw jj =>
    simp only [LdWarp.lcn, hsite, Loader.arrAt, Loader.inPkt, Nat.add_zero] at hcm
    refine ⟨n (.load .commit) + jj.val, ⟨?_, fun h3 => ?_⟩, fun {pc q l ok acq sc} hev => ?_⟩
    · have := hok ⟨(n (.load .commit) + jj.val) % 3, Nat.mod_lt _ (by decide)⟩
      rw [this, hsite]
      exact Loader.ringCnt_mod _
    · simp only [Loader.LFits, hsite, Loader.lc] at hF
      obtain ⟨l, -, hFE, h1, h2⟩ := hF
      have hj := jj.isLt
      cases l with
      | false => have := h2 rfl; omega
      | true =>
        obtain ⟨⟨R', bal, hP, hr⟩, hA⟩ := h1 rfl
        have hR : MmaRounds p L g _ := ⟨R', bal, hP, rfl⟩
        have hle := pkts_rounds hP hR
        rw [← hr, ← hA] at hle
        refine ⟨_, hR, by omega, .inl ?_⟩
        simp only [Progress.time, Progress.roleTime, Progress.Ld.time, hsite]
        omega
    · cases ld_use (l := l) hp hRing hev rfl with
      | dw j' ok' hs' hl hk =>
        rw [hsite] at hs'
        cases hs'
        refine ⟨by rw [hl, hcm], ?_⟩
        simp only [Kind.wait.injEq] at hk
        obtain ⟨-, rfl, -⟩ := hk
        obtain ⟨s, v, kk'⟩ := d
        simp only at hsite
        subst hsite
        rw [ldPar, Nat.mod_mod, Loader.dw_par hRing, hcm]
      | _ => simp_all

end
end
end PTX.Kernels.TmlFa4Fwd.Proof
