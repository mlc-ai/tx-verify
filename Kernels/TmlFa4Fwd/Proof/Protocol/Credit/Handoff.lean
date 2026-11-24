-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Credit.Named
public import Kernels.TmlFa4Fwd.Proof.Protocol.Credit.Obj
public import Lemmas.Protocol.UnitGate
import Kernels.TmlFa4Fwd.Proof.Lib.PollSpin
import Lemmas.Protocol.PollIndex
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The credit hand-off

Stage `st`'s credit barrier is gated by its softmax polls (`creditGate`, `MbarRing.Unit.Gate`):
correction lane `a` is paired with the softmax lanes of the stage's warp with its rows. Its credit
arrival of use `s` follows its `bar.sync` of ordinal `s`, whose generation the paired lane's
`bar.arrive` of ordinal `s` joins (a witness of the return), which follows the lane's credit poll
with `s` earlier successful ones, a canonical spin. So the softmax poll with `q + 1` earlier ones
synchronizes with every correction lane's arrival with `q` earlier ones (`creditHandoff`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow CtaBarrier

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- Every successful poll of the kernel is a canonical spin. -/
theorem poll_spin (hX : Consistent L kernel Assumptions.all m X) :
    ∀ w pc m q acq sc, X.get w = some ⟨pc, .wait m q true acq sc⟩ →
      ∃ exit, kernel.CanonicalSpin pc exit :=
  fun _ _ _ _ _ _ he => poll_canonical hX he

/-- A thread of a launched thread's CTA is launched. -/
theorem thread_lt_of_cta {g h : Nat} (hg : g < L.threads) (hc : h / L.block = g / L.block) :
    h < L.threads := by
  simp only [Launch.threads] at hg ⊢
  have hb : 0 < L.block := by
    rcases Nat.eq_zero_or_pos L.block with h0 | h0
    · rw [h0, Nat.mul_zero] at hg; omega
    · exact h0
  rw [← Nat.div_lt_iff_lt_mul hb] at hg ⊢
  omega

theorem corrLane_facts (hp : Pre p L m) (c : Nat) (a : Fin 128) :
    corrLane L c a / L.block = c ∧ Prologue.warpIndex L (corrLane L c a) = 8 + a.val / 32 := by
  have hb := hp.block
  have ha := a.isLt
  unfold corrLane Prologue.warpIndex
  rw [hb]
  constructor <;> omega

/-- The softmax lanes of stage `st` of lane `g`'s CTA. -/
def SoftIn (L : Launch) (g st h : Nat) : Prop :=
  h < L.threads ∧ h / L.block = g / L.block ∧ Prologue.warpIndex L h < 8 ∧
    Prologue.warpIndex L h / 4 = st

/-- Softmax lane `h` is of the warp of stage `st` that handles correction lane `a`'s rows. -/
def SoftPair (L : Launch) (g st : Nat) (a : Fin 128) (h : Nat) : Prop :=
  h / L.block = g / L.block ∧ Prologue.warpIndex L h = a.val / 32 + 4 * st

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

/-- **The statistics witness**: a passed `bar.sync` of correction lane `y` with ordinal `G` on
`statId st k` and an event of its softmax warp's lane `h` with that ordinal, from which the return
follows; that event follows the lane's credit poll with `G` earlier ones. -/
theorem stat_rendezvous {y j pc st k h : Nat} (hst : st < 2) (hk : k < 4)
    (hy : X.get (y, j) = some ⟨pc, .bar (statId st k) (some 64) .sync⟩)
    (hpass : j + 1 < (X.tr y).length) (hc : h / L.block = y / L.block)
    (hw : Prologue.warpIndex L h = k + 4 * st) :
    ∃ i pc', X.get (h, i) = some ⟨pc', .bar (statId st k) (some 64) .arrive⟩ ∧
      barOrd X h i (statId st k) = barOrd X y j (statId st k) ∧
      Witness L X (.thread (h, i)) (y, j) := by
  have hylt := Frame.lt_of_get hX hy
  have hh := thread_lt_of_cta hylt hc
  have hf : X.IsBarrier (y, j) (statId st k) (some 64) pc := hy
  obtain ⟨i, pc', cnt, md, hi, hord⟩ := softArrives hp hX hFw hst hk hf hpass hc hw
  obtain ⟨rfl, hmd⟩ := stat_of_bar hp hX hFw hk hst hi
  have hmd' : md = .arrive := by
    rcases hmd with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · omega
  subst hmd'
  refine ⟨i, pc', hi, hord, ?_⟩
  have hS := stat_sources hp hX hFw hst hk
  have hG := stat_shape hp hst hk
  have hsame : SameCta L h y := ⟨hh, hylt, hc⟩
  have hke := hS.arrive_key_of_credit hX hG hi hh hsame.2.2.symm hf hpass hord.symm
  obtain ⟨key, hkf, hdone⟩ := ctaBarDone_of_returned hX hf hpass
  have hkey := hS.arrival_key hX hG hf (CtaBarK.arrival hkf)
  simp only at hkey hke
  unfold barOrd at hord
  rw [hkey, ← hord] at hkf hdone
  obtain ⟨ic, hcomp⟩ := hdone
  exact Witness.of_ctaBarCounted hkf hcomp hke hsame.2.2

/-- **The gate path.** -/
theorem credit_path (st : Fin 2) {a : Fin 128} {h i pc : Nat} {sc : MbarScope}
    (hpair : SoftPair L g st.val a h)
    (he : X.get (corrLane L (g / L.block) a, i) =
      some ⟨pc, .arrive (obj L g (192 + 8 * st.val)) 0 1 true sc⟩) :
    ∃ j pc' par acq sc',
      X.get (h, j) = some ⟨pc', .wait (obj L g (192 + 8 * st.val)) par true acq sc'⟩ ∧
      okPolls (obj L g (192 + 8 * st.val)) ((X.tr h).take j) + 1 =
        arrivals (obj L g (192 + 8 * st.val))
          ((X.tr (corrLane L (g / L.block) a)).take i) + 1 ∧
      Relation.TransGen (DepStep L kernel X) (.thread (h, j), true)
        (.thread (corrLane L (g / L.block) a, i), false) := by
  obtain ⟨hcy, hwy⟩ := corrLane_facts (L := L) hp (g / L.block) a
  set y := corrLane L (g / L.block) a with hydef
  have ha := a.isLt
  have hst := st.isLt
  have hk : a.val / 32 < 4 := by omega
  have hylt := Frame.lt_of_get hX he
  have hob : obj L g (192 + 8 * st.val) = obj L y (192 + 8 * st.val) := (obj_cta hcy _).symm
  rw [hob] at he ⊢
  have hcc := corr_credit_arr hp hX hFw (by omega) (by omega) st he
  set s := arrivals (obj L y (192 + 8 * st.val)) ((X.tr y).take i) with hsdef
  rw [hwy, show 8 + a.val / 32 - 5 + 4 * st.val = statId st.val (a.val / 32) by
    unfold statId; omega] at hcc
  obtain ⟨z, pcz, cntz, mz, hzi, hzget, hzo⟩ := exists_bar (X := X) (g := y) (x := i)
    (id := statId st.val (a.val / 32)) (c := s) hcc.ge
  obtain ⟨rfl, hmz⟩ := stat_of_bar hp hX hFw hk hst hzget
  have hmz' : mz = .sync := by
    rcases hmz with ⟨h1, -⟩ | ⟨-, h2⟩
    · omega
    · exact h2
  subst hmz'
  have hpass : z + 1 < (X.tr y).length := by
    have := len_of_get he; simp only at this; omega
  obtain ⟨hch, hwh⟩ := hpair
  obtain ⟨i', pc', hhget, hord, hwit⟩ := stat_rendezvous hp hX hFw hst hk hzget hpass
    (hch.trans hcy.symm) hwh
  -- the softmax lane's credit poll with `s` earlier ones
  have hcr : okPolls (obj L y (192 + 8 * st.val)) ((X.tr h).take i') = s + 1 := by
    rcases soft_bar hp hX hFw (by omega) hhget with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ |
      ⟨-, -, -, h1, -⟩
    · unfold statId at h0; omega
    · unfold statId at h0; omega
    · unfold statId at h0; omega
    · have ho : sobj L h 192 = obj L y (192 + 8 * st.val) := by
        rw [sobj, ← obj_cta (hch.trans hcy.symm)]
        congr 1
        rw [hwh]; omega
      rw [ho] at h1
      rw [h1]
      change barOrd X h i' _ + 1 = _
      rw [hord, hzo]
  obtain ⟨j, pcw, par, acq, scw, hji, hwget, hjq⟩ :=
    MbarRing.Poll.exists_nth (X := X) (m := obj L y (192 + 8 * st.val)) (g := h) (k := i')
      (n := s) (by omega)
  have hnth : MbarRing.Poll.nth X (obj L y (192 + 8 * st.val)) h s = j := by
    rw [← hjq, MbarRing.Poll.nth_eq hwget]
  have g1 := MbarRing.Poll.guard (m := obj L y (192 + 8 * st.val)) (g := h) (k := i')
    (poll_spin hX) (len_of_get hhget) (n := s) (by omega)
  rw [hnth] at g1
  have g2 : Resumes kernel X (y, z) (y, i) :=
    Resumes.of_blocking hzget (b := false) rfl ⟨rfl, hzi, len_of_get he⟩
  refine ⟨j, pcw, par, acq, scw, hwget, by omega, ?_⟩
  exact ((Relation.TransGen.single (DepStep.of_resumes L g1)).tail
    (DepStep.of_witness L hwit)).tail (DepStep.of_resumes L g2)

/-- **Stage `st`'s credit barrier is gated by the softmax polls.** -/
theorem creditGate (g : Nat) (st : Fin 2) :
    MbarRing.Unit.Gate L kernel Assumptions.all X (obj L g (192 + 8 * st.val)) 128
      (corrLane L (g / L.block)) 1 (SoftIn L g st.val) (SoftPair L g st.val) where
  toObj := creditObj hp hX hFw g st
  cover h hh := by
    obtain ⟨-, hc, hw8, hws⟩ := hh
    have hb := hp.block
    refine ⟨⟨h % L.block % 128, by omega⟩, hc, ?_⟩
    unfold Prologue.warpIndex at *
    rw [hb] at *
    simp only
    omega
  partner a := by
    have hb := hp.block
    have ha := a.isLt
    have hst := st.isLt
    refine ⟨g / L.block * L.block + (128 * st.val + a.val), ?_, ?_⟩ <;>
      simp only [Prologue.warpIndex, hb] <;> omega
  gate hpair he _ := credit_path hp hX hFw st hpair he
  acq hh he := (credit_poll hp hX hFw st he).2.1
  cta a h hh := by
    obtain ⟨hlt, hc, -, -⟩ := hh
    have hcy := (corrLane_facts (L := L) hp (g / L.block) a).1
    exact ⟨thread_lt_of_cta hlt (hcy.trans hc.symm), hlt, hcy.trans hc.symm⟩

/-- **The credit hand-off**: a softmax lane's credit poll with `q + 1` earlier successful ones
synchronizes with every correction lane's credit arrival with `q` earlier ones. -/
theorem creditHandoff (g : Nat) (st : Fin 2) :
    MbarRing.UnitHandoff L X (obj L g (192 + 8 * st.val))
      (fun y => ∃ a, y = corrLane L (g / L.block) a) (SoftIn L g st.val) 1 :=
  (creditGate hp hX hFw g st).handoff hX

end

end
end PTX.Kernels.TmlFa4Fwd.Proof
