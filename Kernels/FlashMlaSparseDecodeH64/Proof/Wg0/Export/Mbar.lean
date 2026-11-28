-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Wg0
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Objs

@[expose] public section

/-! # Warpgroup 0's mbarrier row

`mbarRow_wg0`: an event of a lane of warps 0–3 at a pc of warpgroup 0's code that names an
mbarrier is fired from a warpgroup-0 state (`wg0_at`, `Common/Where.lean`) at one of the six
mbarrier sites (any other site names none, `evK_noMbarOf`), on the site's object
(`Wg0/Objs.lean`). The reference invariant's counts are the lane's prefix counts of successful
polls and arrivals (`wg0_okPolls`, `wg0_arrivals`, `Common/Wg0Lane.lean`): in block `r` each ring
family's count is `r` (`polls4`, `polls2`, `arrs4`, `arrs2`), so the slots and parities of the
state's words (`LoopOk`) are those of `Wg0Use`; in the epilogue the QK count is the number of
blocks `R` and the SV slot and parity are the last block's (`EpiOk`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Row `MbarRow.Wg0`**: every event of a lane of warps 0–3 at a pc of warpgroup 0's code that
names an mbarrier is one of `Wg0Use`. -/
theorem mbarRow_wg0 (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : MbarRow.Wg0 P L X := by
  intro g k e l _ he hat hm
  have hub : ∀ f, e.kind ≠ .ub f := by
    intro f hk
    obtain ⟨pc, kd⟩ := e
    simp only at hk
    subst hk
    simp [Frame.MbarOf] at hm
  obtain ⟨hw, hr⟩ := hat
  obtain ⟨d, hR, hev, -⟩ := wg0_at hp hX hFw he hub hr
  obtain ⟨hc, -⟩ := hR (wg0_take_noUb hX he)
  clear hR
  have hP := wg0_okPolls hp hX hFw hw k
  have hA := wg0_arrivals hp hX hFw hw k
  obtain ⟨hpc, hk⟩ := hev
  cases hs : d.site.mb
  · exact absurd hm (Wg0.evK_noMbarOf hs hub hk)
  obtain ⟨site, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨pc, kd⟩ := e
  simp only at hpc hk hub hs ⊢
  subst hpc
  clear he hr
  cases site <;> simp only [Wg0.Site.mb, Bool.false_eq_true] at hs <;>
    simp only [Wg0.EvK, Wg0.ArrEv, Wg0.PollEv] at hk <;>
    simp only [Wg0.RefCore, Wg0.RefAt, Wg0.Site.reg, Wg0.Site.idx, Wg0.Control.D.words] at hc
  case arrL =>
    rcases hk with hk | ⟨f, hk⟩
    · subst hk
      simp only [Frame.MbarOf] at hm
      exact .lastStore rfl (hm.trans (Wg0.arr_loc hp)) (by rw [hm]; rfl)
    · exact absurd hk (hub f)
  case wv =>
    obtain ⟨r, ⟨-, -, -, -, -, hvs, hpv, -⟩, hn, -⟩ := hc
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · subst hk
      simp only [Frame.MbarOf] at hm
      simp only at hvs hpv hn
      subst hvs hpv
      have h4 : polls4 L g .coordReady ((X.tr g).take k) = r := by
        unfold polls4
        rw [hP, hP, hP, hP, hn, hn, hn, hn, Wg0.acq_ready hp _ _ 0, Wg0.acq_ready hp _ _ 1,
          Wg0.acq_ready hp _ _ 2, Wg0.acq_ready hp _ _ 3]
        simp [Wg0.use, Wg0.ind, ringUses]
        omega
      have hl' : l = loc L g (.coordReady (slot4 r)) := hm.trans (Wg0.vReady_loc hp (slot4 r))
      have h1 : okPolls l ((X.tr g).take k) = r / 4 := by
        rw [hP, hn, hl', Wg0.acq_ready hp]
        simp [Wg0.use, Wg0.ind, ringUses, slot4]
        omega
      refine .coordReady rfl (by rw [h4]; exact hl') ⟨ok, ?_⟩
      rw [h1, ← hm, Wg0.parW_W (Nat.mod_lt _ (by decide))]
    · exact absurd hk (hub f)
  case wq =>
    obtain ⟨r, ⟨-, -, -, -, -, -, -, hsl, hps⟩, hn, -⟩ := hc
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · subst hk
      simp only [Frame.MbarOf] at hm
      simp only at hsl hps hn
      subst hsl hps
      have h2 : polls2 L g .qkDone ((X.tr g).take k) = r := by
        unfold polls2
        rw [hP, hP, hn, hn, Wg0.acq_qk hp _ _ 0, Wg0.acq_qk hp _ _ 1]
        simp [Wg0.use, Wg0.ind, ringUses]
        omega
      have hl' : l = loc L g (.qkDone (slot2 r)) := hm.trans (Wg0.qk_loc hp (slot2 r))
      have h1 : okPolls l ((X.tr g).take k) = r / 2 := by
        rw [hP, hn, hl', Wg0.acq_qk hp]
        simp [Wg0.use, Wg0.ind, ringUses, slot2]
        omega
      refine .qkDone rfl (by rw [h2]; exact hl') ⟨ok, ?_⟩
      rw [h1, ← hm, Wg0.parW_W (Nat.mod_lt _ (by decide))]
    · exact absurd hk (hub f)
  case arrV =>
    obtain ⟨r, ⟨-, -, -, -, -, hvs, -⟩, -, hn⟩ := hc
    rcases hk with hk | ⟨f, hk⟩
    · subst hk
      simp only [Frame.MbarOf] at hm
      simp only at hvs hn
      subst hvs
      have h4 : arrs4 L g .coordFree ((X.tr g).take k) = r := by
        unfold arrs4
        rw [hA, hA, hA, hA, hn, hn, hn, hn, Wg0.arr_free hp _ _ _ 0, Wg0.arr_free hp _ _ _ 1,
          Wg0.arr_free hp _ _ _ 2, Wg0.arr_free hp _ _ _ 3]
        simp [Wg0.use, Wg0.ind, ringUses]
        omega
      refine .coordFree rfl ?_ (by rw [hm]; rfl)
      rw [h4]
      exact hm.trans (Wg0.vFree_loc hp (slot4 r))
    · exact absurd hk (hub f)
  case arrS =>
    obtain ⟨r, ⟨-, -, -, -, -, -, -, hsl, -⟩, -, hn⟩ := hc
    rcases hk with hk | ⟨f, hk⟩
    · subst hk
      simp only [Frame.MbarOf] at hm
      simp only at hsl hn
      subst hsl
      have h2 : arrs2 L g .soReady ((X.tr g).take k) = r := by
        unfold arrs2
        rw [hA, hA, hn, hn, Wg0.arr_so hp _ _ _ 0, Wg0.arr_so hp _ _ _ 1]
        simp [ringUses]
        omega
      refine .soReady rfl ?_ (by rw [hm]; rfl)
      rw [h2]
      exact hm.trans (Wg0.so_loc hp (slot2 r))
    · exact absurd hk (hub f)
  case wsv =>
    obtain ⟨⟨hsl, hps⟩, hn, -⟩ := hc
    rcases hk with ⟨ok, hk⟩ | ⟨f, hk⟩
    · subst hk
      simp only [Frame.MbarOf] at hm
      simp only [Nat.reduceEqDiff, ↓reduceIte] at hsl hps hn
      subst hsl hps
      have h2 : polls2 L g .qkDone ((X.tr g).take k) = Wg0.rounds l0 l1 := by
        unfold polls2
        rw [hP, hP, hn, hn, Wg0.acq_qk hp _ _ 0, Wg0.acq_qk hp _ _ 1]
        simp [Wg0.use, Wg0.ind, ringUses]
        omega
      refine .svDone rfl ?_ ⟨ok, ?_⟩
      · rw [h2]
        exact hm.trans (Wg0.sv_loc hp (slot2 _))
      · rw [h2, ← hm, Wg0.parW_W (Nat.mod_lt _ (by decide))]
    · exact absurd hk (hub f)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
