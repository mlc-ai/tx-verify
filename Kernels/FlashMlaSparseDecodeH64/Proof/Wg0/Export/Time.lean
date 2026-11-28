-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Wait
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Slots
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Wg0
public import Lemmas.Kernel.Progress.NextEv
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantAt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.LastTime
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.SubWon
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Class
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Nc
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.EarlyCore

@[expose] public section

/-! # Warpgroup 0's time without a next event

The facts of a lane read off its last state (`w0_end`), for producers that may have no next event:
`wg0_lastEarly`, `wg0_lastExit`, `wg0_soEarly`, `wg0_soExit`, `wg0_cfEarly`, `wg0_cfExit`. The
facts at a next event are in `Wg0/Export/Wait.lean` (imported publicly). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {y : Nat} {e : Event}

/-! ### Without a next event: the lane's last state -/

/-- No undefined behaviour in a prefix of the lane. -/
private theorem w0_noUb {c : Event → Bool} (hc : ∀ f, c f = true → ∃ fl, f.kind = .ub fl)
    (hub : ¬ HasUb X) (i : Nat) : ((X.tr y).take i).countP c = 0 :=
  List.countP_eq_zero.mpr fun f hf hcl => hub (by
    obtain ⟨j, -, hj⟩ := get_lt_of_mem_take hf
    obtain ⟨fl, hk⟩ := hc f hcl
    obtain ⟨pc, kd⟩ := f
    simp only at hk
    subst hk
    exact ⟨(y, j), pc, fl, hj⟩)

/-- **A state of a lane of warps 0–3**: a startup state before time `100`, or a warpgroup-0 state
with the reference invariant at the prefix counts and the launch facts. -/
private theorem w0_state (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) (hw : warp L y < 4) (hg : y < L.threads) {i : Nat}
    {σ : (thread P L y).D} (hσ : Frame.stateAt (thread P L) X y i = some (some σ)) :
    time P L y σ < 100 ∨ ∃ d n, σ = (.inr ⟨.inl .wg0, d⟩, n) ∧
      time P L y σ = wg0Org + Wg0.place d ∧
      Wg0.RefCore L y d (fun c => ((X.tr y).take i).countP (Wg0.cls c)) ∧
      Wg0.LaunchOk P L y d ∧
      ∀ l, arrivals l ((X.tr y).take i) = ((X.tr y).take i).countP (Wg0.cls (.arrive l)) := by
  have hJ := (follow_iff.mp hFw y hg i).2 σ hσ
  obtain ⟨s, n⟩ := σ
  rcases s with d | ⟨e | r, d⟩
  · left
    have hx : Startup.exitOf d = none := by simpa [startupEnter] using glue_gate hσ
    exact Startup.time_lt hx
  · cases e with
    | wg0 =>
      obtain ⟨-, ⟨hR, -⟩, -, -⟩ := hJ
      have hc : (fun c => n (.wg0 c)) = fun c => ((X.tr y).take i).countP (Wg0.cls c) :=
        funext fun c => state_count hσ (.wg0 c)
      have hu : n .ub = 0 := (state_count hσ .ub).trans
        (w0_noUb (fun f h => by obtain ⟨pc, kd⟩ := f; cases kd <;> simp [cls] at h ⊢) hub i)
      have hR' := hR hu
      rw [hc] at hR'
      obtain ⟨hC, hL, -⟩ := hR' (w0_noUb (fun f h => by
        obtain ⟨pc, kd⟩ := f
        cases kd with
        | ub fl => exact ⟨fl, rfl⟩
        | wait l q ok a sc => cases ok <;> simp [Wg0.cls, Wg0.kindOf] at h
        | tc t => cases t <;> simp [Wg0.cls, Wg0.kindOf] at h
        | _ => simp [Wg0.cls, Wg0.kindOf] at h) hub i)
      exact .inr ⟨d, n, rfl, rfl, hC, hL, fun l => wg0_arrivals hp hX hFw hw i l⟩
    | dequant | wg1 =>
      obtain ⟨-, -, -, h⟩ := hJ
      simp only [Entry.wg, wgOf, tidOf] at h
      simp only [warp] at hw
      omega
  · exact hJ.elim

/-- **The lane's last state**: the principle behind the facts without a next event. A property
of every time `t ≤ 100`, and of `wg0Org + place d + δ` (`δ ≤ 1`) for every warpgroup-0 state `d`
of a prefix with its reference invariant, holds of the lane's time. -/
private theorem w0_end (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) (hw : warp L y < 4) (hg : y < L.threads)
    {Q : Nat → Prop} (hpro : ∀ t, t ≤ 100 → Q t)
    (hst : ∀ i δ (d : Wg0.Control.D), i ≤ (X.tr y).length → δ ≤ 1 →
      Wg0.RefCore L y d (fun c => ((X.tr y).take i).countP (Wg0.cls c)) →
      Wg0.LaunchOk P L y d →
      (∀ l, arrivals l ((X.tr y).take i) = ((X.tr y).take i).countP (Wg0.cls (.arrive l))) →
      Q (wg0Org + Wg0.place d + δ)) :
    Q (Sched.threadTime (timed P L) X y) := by
  have step : ∀ i δ σ, i ≤ (X.tr y).length → δ ≤ 1 →
      Frame.stateAt (thread P L) X y i = some (some σ) → Q (time P L y σ + δ) := by
    intro i δ σ hi hδ hσ
    rcases w0_state hp hX hFw hub hw hg hσ with ht | ⟨d, n, rfl, ht, hC, hL, hA⟩
    · exact hpro _ (by omega)
    · rw [ht]
      exact hst i δ d hi hδ hC hL hA
  refine time_last (hpro 0 (by omega)) (fun σ hs => ?_) (fun σ _ hs _ _ => ?_)
  · simpa using step _ 0 σ (Nat.le_refl _) (Nat.zero_le 1) hs
  · exact step _ 1 σ (by omega) (Nat.le_refl 1) hs

/-- **A lane of warpgroup 0 not arrived on `last_store_done` is at most one past the arrival's
slot**, in an execution without undefined behaviour (no next event needed). -/
theorem wg0_lastEarly (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) (hw : warp L y < 4) (hg : y < L.threads)
    (h0 : arrivals (loc L y .lastStoreDone) (X.tr y) = 0) :
    Sched.threadTime (timed P L) X y ≤ lastArr + 1 := by
  refine w0_end hp hX hFw hub hw hg (Q := fun t => t ≤ lastArr + 1)
    (fun t ht => by simp only [lastArr, wg0Org, w0ArrL]; omega)
    (fun i δ d _ hδ hC hL hA => ?_)
  have hle : arrivals (loc L y .lastStoreDone) ((X.tr y).take i) ≤
      arrivals (loc L y .lastStoreDone) (X.tr y) := (List.take_sublist i _).countP_le
  rcases Wg0.early_core hC hL with ⟨a, r, i', hC', h5, -⟩ | hC'
  · have h := (hA _).trans (hC' (loc L y .lastStoreDone))
    cases a
    · have := h5 rfl
      simp only [lastArr, wg0Org, w0ArrL]
      omega
    · rw [show arrivals (loc L y .lastStoreDone) ((X.tr y).take i) = 0 by omega] at h
      simp [Wg0.arrCnt, Wg0.o_last hp, Wg0.o_vFree hp, Wg0.o_so hp, Wg0.loc_inj, Wg0.ind] at h
  · have h := (hA _).trans (hC' (loc L y .lastStoreDone))
    rw [show arrivals (loc L y .lastStoreDone) ((X.tr y).take i) = 0 by omega] at h
    simp [Wg0.arrCnt, Wg0.o_last hp, Wg0.o_vFree hp, Wg0.o_so hp, Wg0.loc_inj, Wg0.ind] at h

/-- **The state behind a lane's `exit`** has made every arrival of the CTA's blocks. -/
private theorem w0_exit (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L y < 4) {k pc : Nat}
    (hx : X.get (y, k) = some ⟨pc, .exit⟩) (h103 : 103 ≤ pc) :
    ∀ l, arrivals l ((X.tr y).take k) =
      Wg0.arrCnt (Wg0.objs L y) true (blocksOf P L (y / L.block)) 0 l := by
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw hx (fun _ h => by cases h)
  have h := state_role hJ hi
  rw [← hpc] at h
  simp only at h
  cases h with
  | wg0 d n hR _ _ _ =>
    have hc : (fun c => n (.wg0 c)) = fun c => ((X.tr y).take k).countP (Wg0.cls c) :=
      funext fun c => state_count hσ (.wg0 c)
    have hR' := hR (state_ub hX hσ hx)
    rw [hc] at hR'
    obtain ⟨hC, hL, -⟩ := hR' (wg0_take_noUb hX hx)
    obtain ⟨-, hK⟩ : Wg0.Ev P L y (warpW L y) d ⟨pc, .exit⟩ := hev
    have hs := Wg0.evK_exit hK rfl
    have hk : (d : Wg0.Control.D).site.reg = .fin := by rw [hs]; rfl
    exact fun l => (wg0_arrivals hp hX hFw hw k l).trans (Wg0.fin_core hC hL hk l)
  | startup _ _ _ _ _ _ hr => omega
  | head _ _ _ _ _ _ hw' => simp only [warp] at hw hw'; omega
  | idle _ _ _ hw' => simp only [warp] at hw; simp only [warpOf, tidOf] at hw'; omega
  | index _ _ _ hw' => simp only [warp] at hw hw'; omega
  | mma _ _ _ _ _ hw' => simp only [warp] at hw hw'; omega
  | tma _ _ _ _ _ hw' => simp only [warp] at hw hw'; omega
  | dequant _ _ _ hw' => simp only [warp] at hw hw'; omega

/-- **A lane of warpgroup 0 that exited has arrived on `last_store_done`** (an exit is past the
startup: `startup_exit`). -/
theorem wg0_lastExit (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L y < 4) {k pc : Nat}
    (hx : X.get (y, k) = some ⟨pc, .exit⟩) (h103 : 103 ≤ pc) :
    1 ≤ arrivals (loc L y .lastStoreDone) (X.tr y) := by
  have h := w0_exit hp hX hFw hw hx h103 (loc L y .lastStoreDone)
  have hle : arrivals (loc L y .lastStoreDone) ((X.tr y).take k) ≤
      arrivals (loc L y .lastStoreDone) (X.tr y) := (List.take_sublist k _).countP_le
  simp [Wg0.arrCnt, Wg0.o_last hp, Wg0.o_vFree hp, Wg0.o_so hp, Wg0.loc_inj, Wg0.ind] at h
  omega

/-- **A lane of warpgroup 0 short of the CTA's uses of `so_ready` slot `b` is at most one past
the arrival slot of its next use** (block `2 A + b`, `A` its arrivals on the slot), in an
execution without undefined behaviour (no next event needed). -/
theorem wg0_soEarly (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) (hw : warp L y < 4) (hg : y < L.threads) (b : Fin 2)
    (hlt : arrivals (loc L y (.soReady b)) (X.tr y) <
      ringUses 2 b.val (blocksOf P L (y / L.block))) :
    Sched.threadTime (timed P L) X y ≤
      soArr (2 * arrivals (loc L y (.soReady b)) (X.tr y) + b) + 1 := by
  have hb := b.isLt
  refine w0_end hp hX hFw hub hw hg
    (Q := fun t => t ≤ soArr (2 * arrivals (loc L y (.soReady b)) (X.tr y) + b) + 1)
    (fun t ht => by simp only [soArr, frame, stride, loopBase, wg0Off, w0ArrS]; omega)
    (fun i δ d _ hδ hC hL hA => ?_)
  have hle : arrivals (loc L y (.soReady b)) ((X.tr y).take i) ≤
      arrivals (loc L y (.soReady b)) (X.tr y) := (List.take_sublist i _).countP_le
  rcases Wg0.early_core hC hL with ⟨a, r, i', hC', -, hS, -⟩ | hC'
  · have h := (hA _).trans (hC' (loc L y (.soReady b)))
    rw [Wg0.arr_so hp] at h
    simp only [soArr, frame, stride, wg0Org, wg0Blk0, wg0Off, loopBase, w0ArrS, ringUses] at *
    omega
  · have h := (hA _).trans (hC' (loc L y (.soReady b)))
    rw [Wg0.arr_so hp] at h; omega

/-- **A lane of warpgroup 0 that exited has made the CTA's uses of `so_ready` slot `b`.** -/
theorem wg0_soExit (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L y < 4) {k pc : Nat} (b : Fin 2)
    (hx : X.get (y, k) = some ⟨pc, .exit⟩) (h103 : 103 ≤ pc) :
    ringUses 2 b.val (blocksOf P L (y / L.block)) ≤ arrivals (loc L y (.soReady b)) (X.tr y) := by
  have h := w0_exit hp hX hFw hw hx h103 (loc L y (.soReady b))
  rw [Wg0.arr_so hp] at h
  exact h ▸ (List.take_sublist k _).countP_le


/-- **A lane of warpgroup 0 short of the CTA's uses of `valid_coord_free` slot `j` is at most one
past the arrival slot of its next use** (block `4 A + j`, `A` its arrivals on the slot), in an
execution without undefined behaviour (no next event needed). -/
theorem wg0_cfEarly (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hub : ¬ HasUb X) (hw : warp L y < 4) (hg : y < L.threads) (j : Fin 4)
    (hlt : arrivals (loc L y (.coordFree j)) (X.tr y) <
      ringUses 4 j.val (blocksOf P L (y / L.block))) :
    Sched.threadTime (timed P L) X y ≤
      cfArrW0 (4 * arrivals (loc L y (.coordFree j)) (X.tr y) + j) + 1 := by
  have hj := j.isLt
  refine w0_end hp hX hFw hub hw hg
    (Q := fun t => t ≤ cfArrW0 (4 * arrivals (loc L y (.coordFree j)) (X.tr y) + j) + 1)
    (fun t ht => by simp only [cfArrW0, frame, stride, loopBase, wg0Off, w0ArrV]; omega)
    (fun i δ d _ hδ hC hL hA => ?_)
  have hle : arrivals (loc L y (.coordFree j)) ((X.tr y).take i) ≤
      arrivals (loc L y (.coordFree j)) (X.tr y) := (List.take_sublist i _).countP_le
  rcases Wg0.early_core hC hL with ⟨a, r, i', hC', -, hS, hV⟩ | hC'
  · have h := (hA _).trans (hC' (loc L y (.coordFree j)))
    rw [Wg0.arr_free hp] at h
    simp only [cfArrW0, frame, stride, wg0Org, wg0Blk0, wg0Off, loopBase, w0ArrV, w0ArrS] at *
    by_cases hc : r % 4 = j.val ∧ 3 ≤ i'
    · simp only [Wg0.use, Wg0.ind, hc, and_self, ↓reduceIte, ringUses] at h
      omega
    · simp only [Wg0.use, Wg0.ind, hc, ↓reduceIte, ringUses] at h
      by_cases hi : i' ≤ 2
      · have := hV hi
        omega
      · omega
  · have h := (hA _).trans (hC' (loc L y (.coordFree j)))
    rw [Wg0.arr_free hp] at h
    simp only [Wg0.use, Wg0.ind, ringUses] at h hlt
    omega

/-- **A lane of warpgroup 0 that exited has made the CTA's uses of `valid_coord_free` slot
`j`.** -/
theorem wg0_cfExit (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (hw : warp L y < 4) {k pc : Nat} (j : Fin 4)
    (hx : X.get (y, k) = some ⟨pc, .exit⟩) (h103 : 103 ≤ pc) :
    ringUses 4 j.val (blocksOf P L (y / L.block)) ≤
      arrivals (loc L y (.coordFree j)) (X.tr y) := by
  have h := w0_exit hp hX hFw hw hx h103 (loc L y (.coordFree j))
  rw [Wg0.arr_free hp] at h
  simp only [Wg0.use, Wg0.ind] at h
  have hle : arrivals (loc L y (.coordFree j)) ((X.tr y).take k) ≤
      arrivals (loc L y (.coordFree j)) (X.tr y) := (List.take_sublist k _).countP_le
  omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
