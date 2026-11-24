-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Ideal
public import Kernels.TmlFa4Fwd.Proof.Lib.Export
public import Kernels.TmlFa4Fwd.Proof.Progress.Time
import Kernels.TmlFa4Fwd.Proof.Common.View
import Kernels.TmlFa4Fwd.Proof.Epilogue.Facts
import Kernels.TmlFa4Fwd.Proof.Epilogue.Ledger
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Epilogue.Open
import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Kernels.TmlFa4Fwd.Proof.Lib.NoPicked
import Kernels.TmlFa4Fwd.Proof.Startup.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Top.Register
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The output lanes' free arrivals: after the ready poll, and their time -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {h k : Nat}

private theorem exit_site {g : Nat} {d : Epilogue.D} {pc : Nat}
    (hev : Epilogue.Ev p L g d ⟨pc, .exit⟩) : ∃ l, d.site = .exit l := by
  obtain ⟨s, rest⟩ := d
  cases s <;> simp only [Epilogue.Ev] at hev
  all_goals (try exact ⟨_, rfl⟩)
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals simp_all [Epilogue.isStore]

/-- **An output lane's free arrival follows its ready poll.** -/
theorem out_free_polled (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L h = 13) {st : Fin 2} {pc tx c : Nat}
    {rel : Bool} {sc : MbarScope}
    (he : X.get (h, k) = some ⟨pc, .arrive (obj L h (224 + 8 * st.val)) tx c rel sc⟩) :
    okPolls (obj L h (208 + 8 * st.val)) ((X.tr h).take k) = 1 := by
  have hh := Frame.lt_of_get hX he
  rcases Epilogue.open_ev hp hX hFw hw he (fun f h => by cases h) with
    ⟨s, n, -, -, -, hi, hev⟩ | ⟨d, n, hσ, -, -, -, hev⟩
  · obtain ⟨c, hc⟩ := start_mbar hev hi.2 (l := obj L h (224 + 8 * st.val)) rfl
    cases hc
  obtain ⟨-, -, -, -, hL⟩ := (Epilogue.fits hp hX hh hw hσ).2
  rcases epi_site hev (l := obj L h (224 + 8 * st.val)) rfl with ⟨st', hs, hl⟩ | ⟨st', hs, hl⟩
  · exfalso
    obtain ⟨site, rest⟩ := d
    simp only at hs
    subst hs
    obtain ⟨ok, hk⟩ := hev
    cases hk
  · obtain rfl : st' = st := by
      have := obj_inj hl
      exact Fin.ext (by omega)
    have h1 := (hL st').1
    simp only [Epilogue.acqd, hs] at h1
    have h2 := count hσ (.poll st')
    rw [h1] at h2
    exact h2

private theorem late_written {s : Epilogue.Site} : Epilogue.written s = Progress.Out.late s := by
  cases s <;> rfl

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
  (hh : h < L.threads) (hw : Prologue.warpIndex L h = 13) (st : Fin 2)
include hp hX hFw hh hw

/-- An output lane before the end of the tail, or its free arrivals are made. -/
theorem out_state {σ : (thread p L h).D}
    (hσ : Frame.stateAt (thread p L) X h k = some (some σ)) :
    Progress.time p L h σ + 1 < Progress.endBase p ∨
      1 ≤ arrivals (obj L h (224 + 8 * st.val)) ((X.tr h).take k) := by
  have hJ := (goodR hp hX hFw hh k).2 σ hσ
  have hsp := Progress.scanBase_le_primeBase p
  have h4 : Progress.scanBase + 4 ≤ Progress.primeBase p := by unfold Progress.primeBase; omega
  have hend : Progress.primeBase p + 1024 ≤ Progress.endBase p := by
    have := Progress.primeBase_le_clk p (Progress.bmax p + 1) 0
    unfold Progress.endBase Progress.tailBase; omega
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨i, d⟩
  · left
    have hS := (Epilogue.good_all hp hX hh hw k).2 _ hσ
    have hx : ∀ r, s.site ≠ .enter r := by
      intro r he
      have h1 := hS.1
      simp only [StartAt, he] at h1
    have h1 := Progress.startTime_lt hx
    simp only [Progress.time]
    omega
  cases i with
  | epilogue =>
    obtain ⟨hF, -, -, -, -, hL⟩ := Epilogue.fits hp hX hh hw hσ
    cases hl : Progress.Out.late d.site with
    | true =>
      right
      have h1 := (hL st).2
      have h2 := count hσ (.freed st)
      have h3 : Epilogue.frees d = 2 := by
        rw [← late_written] at hl
        revert hl
        cases hs : d.site <;> simp [Epilogue.frees, Epilogue.written, hs]
        all_goals exact fun h => by simp [h]
      simp only [Epilogue.freedAt, h3] at h1
      have : st.val < 2 := st.isLt
      simp only [this, ite_true] at h1
      change ((X.tr h).take k).countP _ = n (.freed st) at h2
      rw [h1] at h2
      exact h2.ge
    | false =>
      left
      cases ht : Progress.Out.tail d.site with
      | true =>
        have := Progress.Out.tailOff_lt d.site
        have hs : d.site ≠ .start := fun hs => by simp [hs, Progress.Out.tail] at ht
        simp only [Progress.time, Progress.roleTime, Progress.Out.time, ht, hs, ite_false, ite_true,
          Progress.endBase, Progress.span]
        omega
      | false =>
        have hl' : d.site.late = false := hl
        have h1 := Epilogue.fits_coll_le hp hF hl'
        have h3 := Progress.pass_lt_prime (p := p) (c := Progress.collCount n)
          (by unfold Progress.collCount Progress.cmax; omega) (Progress.Out.coll d.site)
        simp only [Progress.time, Progress.roleTime, Progress.Out.time, ht, hl, Bool.false_eq_true,
          ite_false]
        split <;> omega
  | softmax => have := (JR.softmax hJ).1; omega
  | correction => obtain ⟨h1, h2, -⟩ := JR.correction hJ (by omega); omega
  | mma => have := (JR.mma hJ).1; omega
  | loader b => have := (JR.loader hJ).1; omega
  | stub r => exact (JR.not_stub hJ).elim

/-- **An output lane that has not freed the stage** is before the second scan. -/
theorem out_early (ha : arrivals (obj L h (224 + 8 * st.val)) (X.tr h) ≤ 0) :
    Sched.threadTime (Progress.timed p L) X h < Progress.endBase p := by
  have key : ∀ k σ, Frame.stateAt (thread p L) X h k = some (some σ) →
      Progress.time p L h σ + 1 < Progress.endBase p := by
    intro k σ hσ
    rcases out_state hp hX hFw hh hw st hσ with h1 | h1
    · exact h1
    · have : arrivals (obj L h (224 + 8 * st.val)) ((X.tr h).take k) ≤
          arrivals (obj L h (224 + 8 * st.val)) (X.tr h) := (List.take_sublist _ _).countP_le
      omega
  have h0 : 0 < Progress.endBase p := by unfold Progress.endBase Progress.span; omega
  unfold Sched.threadTime
  split
  · rename_i d hd; exact Nat.lt_of_succ_lt (key _ d hd)
  · exact h0
  · split
    · rename_i d hd; exact key _ d hd
    · exact h0

/-- **An output lane of a CTA with a tile exits** after it freed both stages. -/
theorem out_exit {pc : Nat} (hT : ∃ R bal, Epilogue.Picked p L h R bal)
    (he : X.get (h, k) = some ⟨pc, .exit⟩) :
    1 ≤ arrivals (obj L h (224 + 8 * st.val)) ((X.tr h).take k) := by
  rcases Epilogue.open_ev hp hX hFw hw he (fun f h => by cases h) with
    ⟨s, n, -, -, -, hi, hev⟩ | ⟨d, n, hσ, -, -, -, hev⟩
  · exfalso
    have hx : exit L h s = none := hi.2
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site with
    | sh j => fin_cases j <;> simp [Startup.Ev] at hev
    | elect j => simp [Startup.Ev] at hev
    | init q => simp [Startup.Ev] at hev
    | fence => simp [Startup.Ev] at hev
    | bar => simp [Startup.Ev] at hev
    | enter r => simp [exit] at hx
  obtain ⟨hF, -, -, -, -, hL⟩ := Epilogue.fits hp hX hh hw hσ
  obtain ⟨l, hs⟩ := exit_site hev
  cases l with
  | false => exact (noPicked_of_exit hF hs hT).elim
  | true =>
    have h1 := (hL st).2
    have h2 := count hσ (.freed st)
    simp only [Epilogue.freedAt, Epilogue.frees, hs, Epilogue.written, ite_true] at h1
    have : st.val < 2 := st.isLt
    simp only [this, ite_true] at h1
    change ((X.tr h).take k).countP _ = n (.freed st) at h2
    rw [h1] at h2
    exact h2.ge

end
end
end PTX.Kernels.TmlFa4Fwd.Proof
