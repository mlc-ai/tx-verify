-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.Lk5VCount
public import Kernels.InklingRelDecode.Proof.Interface.Lk4Class
public import Kernels.InklingRelDecode.Proof.Interface.Lk5BAlign

@[expose] public section

/-!
# The warp-collective `tcgen05` events before a default-partition state

The events of the class `isTcColl` (allocation, relinquishment, deallocation, `tcgen05.ld`, `.st`
and their waits) of a default-partition thread are counted by its state and the number of
`bar24` states before it (`B0N.nB24`, the rescale iterations it ran):

* the common start: the allocation and the relinquishment, in warp 0 only (`w0`);
* the softmax region: four per iteration (`ldS`, `waitLd`, `tmemSt`, `tmemWait`), four more per
  rescale iteration (`ldO`, `waitLdO`, `stO`, `waitStO`), and the offset of the site in its
  iteration (`smO`);
* the epilogue: the load and its wait unless `num_iters < 1` (`sk`), the deallocation in warp 0.

`tc_inv`: the count before every state of a default-partition thread is
`tcF s + 4 nB24`. The induction is `Lk.cnt_inv`'s, with `Lk.isTcColl_state` for the class of
each event.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress.Wx
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface PTX.Kernels.InklingRelDecode.Proof.Lk5B
open PTX.Kernels.InklingRelDecode.Proof.Interface.B0N

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- One for a thread of warp 0 (the allocating warp). -/
def w0 (L : Launch) (g : Nat) : Nat := if g % L.block < 32 then 1 else 0

/-- The common start's count. -/
def dsTc (L : Launch) (g : Nat) : DStart.Site → Nat
  | .alloc => 0
  | .shfl | .toProA => 2 * w0 L g
  | _ => w0 L g

/-- The offset of a softmax site in its iteration (the rescale path's four events are counted by
`bar24`). -/
def smO : Sm.Site → Nat
  | .waitLd | .waitStO => 1
  | .shfl5 | .shfl6 | .bar22 | .shfl7 | .shfl8 | .shfl9 | .shfl10 | .store10 | .bar23 | .ldL
  | .shfl11 | .shfl12 | .waitO | .ldO | .bar20 | .tmemSt => 2
  | .waitLdO | .tmemWait => 3
  | .bar24 | .bar21 | .arrive => 4
  | _ => 0

/-- The epilogue's offset: the load and its wait (not when `sk`), the deallocation (warp 0). -/
def epO (sk : Bool) (w : Nat) (s : Epi.Site) : Nat :=
  if s = .wait ∨ s = .shfl ∨ s = .ld then 0 else if s = .waitLd then 1
  else if s = .exit then (if sk then 0 else 2) + w else if sk then 0 else 2

/-- **The count of a default-partition state** (without the rescale iterations' `4 nB24`). -/
def tcF (Q : Params) (L : Launch) (g : Nat) : DComp.St → Nat
  | .dstart d => dsTc L g d.site
  | .pro _ => 2 * w0 L g
  | .sm d => 2 * w0 L g + 4 * d.i + smO d.site
  | .epi d => 2 * w0 L g + 4 * Lk.NI Q L g + epO d.sk (w0 L g) d.site

/-- The side fact of the common start: the allocation and the relinquishment are warp 0's. -/
def tcSide (L : Launch) (g : Nat) : DComp.St → Prop
  | .dstart d => d.site = .alloc ∨ d.site = .relinq → g % L.block < 32
  | .epi d => d.site = .dealloc → g % L.block < 32
  | _ => True

/-- The class bit of a state. -/
def tcB (s : DComp.St) : Nat := if Lk.dTc s = true then 1 else 0

/-- The `bar24` bit of a state. -/
def b24B (s : DComp.St) : Nat := if isB24 s = true then 1 else 0

/-! ### One step of each region -/

theorem sm_tc_next {d d' : Sm.D} {e : Event} (h : Sm.next L g d e = some (some d')) :
    4 * d'.i + smO d'.site + 4 * b24B (.sm d) = 4 * d.i + smO d.site + tcB (.sm d) := by
  obtain ⟨s, en, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  cases s <;>
    simp only [Sm.next, Sm.afterArrive, Sm.afterSetup] at h <;>
    (repeat' split at h) <;>
    first
    | (simp at h; done)
    | (simp only [toBar20_iff] at h
       obtain ⟨-, rfl⟩ := h
       simp_all [smO, b24B, tcB, isB24, Lk.dTc, Sm.D.upd, Sm.D.afterSum])
    | (obtain rfl := Option.some.inj (Option.some.inj h)
       simp_all [smO, b24B, tcB, isB24, Lk.dTc, Sm.D.afterSum] <;> omega)

theorem epi_tc_next {d d' : Epi.D} {e : Event} (h : Epi.next d e = some (some d'))
    (hl : Epi.epLoad d.site = true → d.sk = false)
    (hp : d.pr.p3 = decide (g % L.block < 32)) (hd : d.site = .dealloc → g % L.block < 32) :
    epO d'.sk (w0 L g) d'.site = epO d.sk (w0 L g) d.site + tcB (.epi d) ∧
      (d'.site = .dealloc → g % L.block < 32) := by
  obtain ⟨s, pr, o, sk⟩ := d
  cases s <;> simp only [Epi.next] at h <;> (repeat' split at h) <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp_all [epO, tcB, Lk.dTc, Epi.D.stores, Epi.stNext, Epi.epLoad, w0] <;>
    (repeat' split_ifs) <;> simp_all

/-- **One step of a default-partition thread** adds its class bit to `tcF + 4 · bar24`. -/
theorem tc_step (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads) {k : Nat} {e : Event} {s t : DComp.St}
    (he : X.get (g, k) = some e) (hσ : St Q L X g k = some (some (.d s)))
    (hn : DComp.next L g Q s e = some (some t)) (hS : tcSide L g s)
    (hC : Lk.cntSide Q L g (.d s)) :
    tcF Q L g t + 4 * b24B s = tcF Q L g s + tcB s ∧ tcSide L g t := by
  cases s with
  | dstart d =>
    change DComp.dstartNext L g Q d e = _ at hn
    unfold DComp.dstartNext at hn
    obtain ⟨d', hd', rfl⟩ := map_map_eq_some_some hn
    obtain ⟨st, tm⟩ := d
    have hb : b24B (.dstart ⟨st, tm⟩) = 0 := by simp [b24B, isB24]
    rw [hb]
    cases st <;> simp only [DStart.next] at hd' <;> (repeat' split at hd') <;>
      simp only [Option.some.injEq, reduceCtorEq] at hd' <;> subst hd' <;>
      simp_all [tcF, dsTc, tcB, Lk.dTc, tcSide, w0, ProA.D.start] <;> split_ifs <;> omega
  | pro d =>
    have hb : b24B (.pro d) = 0 := by simp [b24B, isB24]
    have ht : tcB (.pro d) = 0 := by simp [tcB, Lk.dTc]
    rw [hb, ht]
    change DComp.proNext L g Q d e = _ at hn
    unfold DComp.proNext at hn
    split at hn
    · split at hn
      · simp only [Option.some.injEq] at hn
        subst hn
        exact ⟨by simp [tcF, SmEntry.d0, smO], trivial⟩
      · cases hn
    · obtain ⟨d', -, rfl⟩ := map_map_eq_some_some hn
      exact ⟨by simp [tcF], trivial⟩
  | sm d =>
    change DComp.smNext L g d e = _ at hn
    unfold DComp.smNext at hn
    split at hn
    · rename_i hl
      unfold DComp.exitNext at hn
      split at hn
      · simp only [Option.some.injEq] at hn
        subst hn
        have h26 := Lk.r26_eq hpre hf hX hg he hσ
        have hb : b24B (.sm d) = 0 := by
          simp [b24B, isB24, (rd_leave (Dc := fun _ => True) hl).2]
        rw [hb]
        refine ⟨?_, by split <;> simp [tcSide, Epi.D.startSk, Epi.D.start, Epi.D.entry]⟩
        simp only [tcF]
        rw [← h26]
        obtain ⟨st, en, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
        split <;>
          (cases st <;> simp only [DComp.leaves] at hl <;>
            simp_all [smO, tcB, Lk.dTc, epO, Epi.D.startSk, Epi.D.start, Epi.D.entry] <;>
            omega)
      · cases hn
    · obtain ⟨d', hd', rfl⟩ := map_map_eq_some_some hn
      have := sm_tc_next hd'
      exact ⟨by simp only [tcF]; omega, trivial⟩
  | epi d =>
    have hb : b24B (.epi d) = 0 := by simp [b24B, isB24]
    rw [hb]
    change (Epi.next d e).map (Option.map DComp.St.epi) = _ at hn
    obtain ⟨d', hd', rfl⟩ := map_map_eq_some_some hn
    have hp : d.pr.p3 = decide (g % L.block < 32) := (hf.reach hg hσ).2.p3
    obtain ⟨h1, h2⟩ := epi_tc_next hd' hC.1 hp hS
    refine ⟨?_, h2⟩
    simp only [tcF, h1]
    omega

/-- **The warp-collective `tcgen05` events before each state of a default-partition thread.** -/
theorem tc_inv (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hg : g < L.threads) :
    ∀ k, k ≤ (X.tr g).length → ∀ {s : DComp.St}, St Q L X g k = some (some (.d s)) →
      Lk.cnt isTcColl X g k = tcF Q L g s + 4 * nB24 Q L X g k ∧ tcSide L g s := by
  intro k
  induction k with
  | zero =>
    intro _ s hσ
    rcases pred_d (Nat.zero_le _) hσ with ⟨-, rfl⟩ | ⟨k0, -, -, h, -⟩
    · simp only [Lk.cnt, List.take_zero, List.countP_nil, nB24, Finset.range_zero,
        Finset.filter_empty, Finset.card_empty, DStart.D.start]
      split <;> simp_all [tcF, dsTc, tcSide, w0]
    · omega
  | succ k ih =>
    intro hk s hσ
    rcases pred_d hk hσ with ⟨h0, -⟩ | ⟨k0, e, s0, hk0, he, hσ0, hn⟩
    · omega
    · have hk0' : k0 = k := by omega
      subst hk0'
      obtain ⟨hc, hS⟩ := ih (by omega) hσ0
      have he' : X.get (g, k0) = some e := he
      have hC := (Lk.cnt_inv hpre hX hf hg k0 (by omega) hσ0).2
      obtain ⟨h1, h2⟩ := tc_step hpre hX hf hg he' hσ0 hn hS hC
      refine ⟨?_, h2⟩
      rw [Lk.cnt_succ _ he, hc, Lk.isTcColl_state hpre hX hf hg he' hσ0, nB24_succ,
        isB24_iff hσ0]
      simp only [b24B, tcB, Lk.tcSt] at h1 ⊢
      by_cases hb : isB24 s0 = true <;> by_cases ht : Lk.dTc s0 = true <;>
        simp only [hb, ht, ↓reduceIte, Bool.false_eq_true] at h1 ⊢ <;> omega

end
end PTX.Kernels.InklingRelDecode.Proof.Progress.Wx
