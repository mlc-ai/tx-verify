-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.DCompTail
public import Kernels.InklingRelDecode.Proof.Thread.SmExit
public import Kernels.InklingRelDecode.Proof.Thread.SmTotG

@[expose] public section

/-!
# The softmax region's obligations, discharged

`DComp.SmObligations` (`DCompTail.lean`) lists what the softmax region owes the default-partition
thread machine: the `Code.StepAt` of `Sm.code` at 17 sites of the score stage (`score`) and the
link from the loop's last event to the bridge (`exit`). This file proves both from the thread-level
step lemmas, and one premise about the launch:

* `score`: `stepAt_score`, from the step lemmas of `SmStgC` (`step_waitLd`), `SmStgB`
  (`step_shfl5`), `SmStgD` (`step_shfl6` to `step_shfl11`, `step_bar22`, `step_store10`,
  `step_bar23`, `step_ldL`, `step_waitO`) and `SmStgE` (`step_ldO`, `step_waitLdO`, `step_bar24`,
  `step_stO`: the O rescale after the test; its guard `%p171` is set by the preceding `mov`, and
  `Inv.re` (`RealSt.al`) gives the number `alpha` reads as for the 64 products).
* `exit`: `exit_of_slack`, from the runs of `SmExit` (the four events that end the loop, the loop
  test and the taken branch to pc 2560, the registers live there depending on the entry numbers,
  the running maximum and sum only) and `Ent.Ok` and `Inv.lb` for the bridge's ranges
  (`exitIn_ok`). The one number the thread proof cannot supply is the room for the output row
  index of the padding rows (`ScoreRest.rowSlack`).

`ScoreRest` is the premise structure; `smObligations_of_rest` is the assembly.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.DComp
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-- **What the thread proof leaves to the layers above**: the room the launch leaves for the
output row index of the padding rows. The bridge reads the row index
`((split * num_tokens + token) + cu_seqlens_q[req]) * 12 + head` in 32-bit arithmetic for every row
of the tile, valid or not (`Br.In.Ok.row`, `Epi.Prm.Ok.row`: below `2 ^ 24`). A padding row has a
token up to 10 and, for the last request, `cu_seqlens_q[req]` up to `num_tokens`, so the index is
below `(num_splits * num_tokens + 11) * 12`; `Pre.outRangeSlack` gives `+ 10` only, which falls
short by one. The field says the bound with `+ 11`, for the entry numbers of every state of the
region; it follows from `Pre` once `Pre.outRangeSlack` is `(num_splits * num_tokens + 11) * 12 *
128 ≤ 2 ^ 31` and the entry numbers are known to be the launch's (`SmEntry.entOf`). -/
structure ScoreRest (Q : Params) (L : Launch) (mem0 : Mem0) (g : Nat) : Prop where
  rowSlack : Pre Q L mem0 → ∀ {d : Sm.D}, Sm.Inv L g d →
    (d.e.splits * d.e.ntok + 11) * 12 * 128 ≤ 2 ^ 31

/-! ### The score stage's sites -/

/-- **The `Code.StepAt` of the region at the 17 sites of the score stage.** -/
theorem stepAt_score {Q : Params} {mem0 : Mem0} (hpre : Pre Q L mem0) (d : Sm.D)
    (hsc : ScoreSite d.site) : (Sm.code Sm.asms L g d).StepAt d := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have hsb : L.sharedBase + 213340 ≤ 2 ^ 18 := by
    have := hpre.sharedRange
    unfold sharedBytes at this
    omega
  cases hs : d.site with
  | waitLd =>
    exact stepAt_of_step d (fun _ => site_mk (by rw [hs]; rfl) Flow.code_tmemWait_1 rfl trivial)
      fun hi h hc hf => Sm.step_waitLd hb hi hs h hc hf
  | shfl5 =>
    exact stepAt_of_step d (fun _ => site_mk (by rw [hs]; rfl) Flow.code_shfl_5 rfl trivial)
      fun hi h hc hf => Sm.step_shfl5 hi hs h hc hf
  | shfl6 =>
    exact stepAt_of_step d (fun _ => site_mk (by rw [hs]; rfl) Flow.code_shfl_6 rfl trivial)
      fun hi h hc hf => Sm.step_shfl6 hi hs h hc hf
  | bar22 =>
    exact stepAt_of_step d (fun _ => site_mk (by rw [hs]; rfl) Flow.code_bar_22 rfl trivial)
      fun hi h hc hf => Sm.step_bar22 hi hs h hc hf
  | shfl7 =>
    exact stepAt_of_step d (fun _ => site_mk (by rw [hs]; rfl) Flow.code_shfl_7 rfl trivial)
      fun hi h hc hf => Sm.step_shfl7 hi hs h hc hf
  | shfl8 =>
    exact stepAt_of_step d (fun _ => site_mk (by rw [hs]; rfl) Flow.code_shfl_8 rfl trivial)
      fun hi h hc hf => Sm.step_shfl8 hi hs h hc hf
  | shfl9 =>
    exact stepAt_of_step d (fun _ => site_mk (by rw [hs]; rfl) Flow.code_shfl_9 rfl trivial)
      fun hi h hc hf => Sm.step_shfl9 hi hs h hc hf
  | shfl10 =>
    exact stepAt_of_step d (fun _ => site_mk (by rw [hs]; rfl) Flow.code_shfl_10 rfl trivial)
      fun hi h hc hf => Sm.step_shfl10 hi hs h hc hf
  | store10 =>
    exact stepAt_of_step d (fun _ => site_mk (by rw [hs]; rfl) Flow.code_store_10 rfl trivial)
      fun hi h hc hf => Sm.step_store10 hi hs h hc hf
  | bar23 =>
    exact stepAt_of_step d (fun _ => site_mk (by rw [hs]; rfl) Flow.code_bar_23 rfl trivial)
      fun hi h hc hf => Sm.step_bar23 hi hs h hc hf
  | ldL =>
    exact stepAt_of_step d (fun _ => site_mk (by rw [hs]; rfl) Flow.code_load_202 rfl trivial)
      fun hi h hc hf => Sm.step_ldL hi hsb hs h hc hf
  | shfl11 =>
    exact stepAt_of_step d (fun _ => site_mk (by rw [hs]; rfl) Flow.code_shfl_11 rfl trivial)
      fun hi h hc hf => Sm.step_shfl11 hi hs h hc hf
  | waitO =>
    exact stepAt_of_step d (fun _ => site_mk (by rw [hs]; rfl) Flow.code_mbarWait_1 rfl trivial)
      fun hi h hc hf => Sm.step_waitO hi hs h hc hf
  | ldO =>
    exact stepAt_of_step d (fun _ => site_mk (by rw [hs]; rfl) Flow.code_tmemLoad_1 rfl trivial)
      fun hi h hc hf => Sm.step_ldO hi hs h hc hf
  | waitLdO =>
    exact stepAt_of_step d (fun _ => site_mk (by rw [hs]; rfl) Flow.code_tmemWait_2 rfl trivial)
      fun hi h hc hf => Sm.step_waitLdO hb hi hs h hc hf
  | bar24 =>
    exact stepAt_of_step d (fun _ => site_mk (by rw [hs]; rfl) Flow.code_bar_24 rfl trivial)
      fun hi h hc hf => Sm.step_bar24 hi hs h hc hf
  | stO =>
    refine stepAt_of_step d (fun _ => site_mk (by rw [hs]; rfl) Flow.code_tmemStore_1 rfl ?_)
      fun hi h hc hf => Sm.step_stO hi hs h hc hf
    show (171, Value.pred (!false)) ∈ Sm.factsAt L g d.site.pc d
    have hm := Flow.mem_factsFrom (val := Sm.valueOf L g d)
      (show 171 ∈ Flow.live 2328 by decide +kernel)
    rw [Sm.valueOf_p171] at hm
    rw [show d.site.pc = 2328 by rw [hs]; rfl]
    exact hm
  | setMaxReg => rw [hs] at hsc; exact absurd hsc (by simp [ScoreSite])
  | bar0 => rw [hs] at hsc; exact absurd hsc (by simp [ScoreSite])
  | pre j => rw [hs] at hsc; exact absurd hsc (by simp [ScoreSite])
  | nxt j => rw [hs] at hsc; exact absurd hsc (by simp [ScoreSite])
  | waitS => rw [hs] at hsc; exact absurd hsc (by simp [ScoreSite])
  | shfl4 => rw [hs] at hsc; exact absurd hsc (by simp [ScoreSite])
  | ldS => rw [hs] at hsc; exact absurd hsc (by simp [ScoreSite])
  | shfl12 => rw [hs] at hsc; exact absurd hsc (by simp [ScoreSite])
  | waitStO => rw [hs] at hsc; exact absurd hsc (by simp [ScoreSite])
  | bar20 => rw [hs] at hsc; exact absurd hsc (by simp [ScoreSite])
  | tmemSt => rw [hs] at hsc; exact absurd hsc (by simp [ScoreSite])
  | tmemWait => rw [hs] at hsc; exact absurd hsc (by simp [ScoreSite])
  | bar21 => rw [hs] at hsc; exact absurd hsc (by simp [ScoreSite])
  | arrive => rw [hs] at hsc; exact absurd hsc (by simp [ScoreSite])

/-! ### The loop's exit -/

/-- **The bridge's numbers are in range at the loop's exit**: the entry numbers (`Ent.Ok`), the
running sum a four-byte word (`Inv.lb`), and the room for the row index of the padding rows. -/
theorem exitIn_ok {d : Sm.D} (hi : Sm.Inv L g d)
    (hs : (d.e.splits * d.e.ntok + 11) * 12 * 128 ≤ 2 ^ 31) (hsb : L.sharedBase % 8 = 0) :
    (exitIn L g d).Ok where
  tid := by
    have := hi.tid
    show g % L.block < Epi.M32
    unfold Epi.M32
    omega
  tm := by
    have := hi.ok.tm
    show d.e.tm < Epi.M32
    unfold Epi.M32
    omega
  w := by
    have := hi.tid
    show g % L.block / 32 < 4
    omega
  c0 := by
    show (d.e.tm + 256) % 2 ^ 32 < Epi.M32
    unfold Epi.M32
    omega
  c0col := by
    have := hi.ok.col
    show (d.e.tm + 256) % 2 ^ 32 + 256 ≤ 2 ^ 16
    omega
  mb := by
    show (L.sharedBase + 213328) % 2 ^ 32 < Epi.M32
    unfold Epi.M32
    omega
  a := by
    have := hi.ok.ntok
    show d.e.ntok < Epi.M32
    unfold Epi.M32
    omega
  b := by
    have := hi.ok.split
    show d.e.split < Epi.M32
    unfold Epi.M32
    omega
  c := by
    have := Sm.tokOf_le (g % L.block)
    show Sm.tokOf (g % L.block) < Epi.M32
    unfold Epi.M32
    omega
  dd := by
    have := hi.ok.qs
    show d.e.qs < Epi.M32
    unfold Epi.M32
    omega
  e := by
    show (d.e.kvh + Sm.remOf (g % L.block)) % 2 ^ 32 < Epi.M32
    unfold Epi.M32
    omega
  n := by
    have := hi.ok.r25
    show d.e.r25 < Epi.M32
    unfold Epi.M32
    omega
  d0 := by
    show Sm.half (g % L.block) * 64 < Epi.M64
    unfold Epi.M64 Sm.half
    omega
  ob := hi.ok.rd75
  lb := hi.ok.rd76
  row := hi.ok.rowIdx_lt hs (g % L.block)
  l := hi.lb
  mb8 := by
    show (L.sharedBase + 213328) % 2 ^ 32 % 8 = 0
    omega
  ob4 := hi.ok.rd75Al
  lb4 := hi.ok.rd76Al

/-- **The exit link**: after an event that ends the loop the thread reaches pc 2560 with the
region's facts, and the bridge's numbers are in range. -/
theorem exit_of_slack {Q : Params} {mem0 : Mem0}
    (hr : Pre Q L mem0 → ∀ {d : Sm.D}, Sm.Inv L g d →
      (d.e.splits * d.e.ntok + 11) * 12 * 128 ≤ 2 ^ 31) :
    Pre Q L mem0 → ∀ {d : Sm.D} {e : Event} {t u : TState} {ins : Instr},
      Sm.Inv L g d → (Sm.code Sm.asms L g d).AtD d t → kernel.code[d.site.pc]? = some ins →
      Fires d.site.pc (eventTmpl Sm.asms L g t ins.op) e (some u) → leaves L g d e →
      (exitIn L g d).Ok ∧ ∃ t', Relation.ReflTransGen (Tau kernel asms L g) u t' ∧
        At t' 2560 (Sm.factsAt L g 2560 d) := by
  intro hpre d e t u ins hi hA hc hf hl
  refine ⟨exitIn_ok hi (hr hpre hi) (by have := hpre.sharedAlignment; omega), ?_⟩
  have h : At t d.site.pc (Sm.facts L g d) := ⟨hA.1, hA.2.1, hA.2.2.1, hA.2.2.2.1, hA.2.2.2.2⟩
  unfold leaves at hl
  cases hs : d.site with
  | bar0 =>
    rw [hs] at hl
    exact Sm.exit_bar0 hi hs hl.1 hl.2 h hc hf
  | pre j =>
    rw [hs] at hl
    obtain ⟨hj, hb, heq⟩ := hl
    refine Sm.exit_pre hi hs (by omega) heq ?_ h hc hf
    intro r bs hk
    rw [hk] at hb
    cases hv : rebuild 3 bs with
    | error f => simp [bf16Read, hv] at hb
    | ok x => exact ⟨x, rfl, by simpa [bf16Read, hv] using hb⟩
  | bar21 =>
    rw [hs] at hl
    exact Sm.exit_bar21 hi hs hl.1 hl.2 h hc hf
  | arrive =>
    rw [hs] at hl
    exact Sm.exit_arrive hi hs hl.2 h hc hf
  | setMaxReg => rw [hs] at hl; exact hl.elim
  | nxt j => rw [hs] at hl; exact hl.elim
  | waitS => rw [hs] at hl; exact hl.elim
  | shfl4 => rw [hs] at hl; exact hl.elim
  | ldS => rw [hs] at hl; exact hl.elim
  | waitLd => rw [hs] at hl; exact hl.elim
  | shfl5 => rw [hs] at hl; exact hl.elim
  | shfl6 => rw [hs] at hl; exact hl.elim
  | bar22 => rw [hs] at hl; exact hl.elim
  | shfl7 => rw [hs] at hl; exact hl.elim
  | shfl8 => rw [hs] at hl; exact hl.elim
  | shfl9 => rw [hs] at hl; exact hl.elim
  | shfl10 => rw [hs] at hl; exact hl.elim
  | store10 => rw [hs] at hl; exact hl.elim
  | bar23 => rw [hs] at hl; exact hl.elim
  | ldL => rw [hs] at hl; exact hl.elim
  | shfl11 => rw [hs] at hl; exact hl.elim
  | shfl12 => rw [hs] at hl; exact hl.elim
  | waitO => rw [hs] at hl; exact hl.elim
  | ldO => rw [hs] at hl; exact hl.elim
  | waitLdO => rw [hs] at hl; exact hl.elim
  | bar24 => rw [hs] at hl; exact hl.elim
  | stO => rw [hs] at hl; exact hl.elim
  | waitStO => rw [hs] at hl; exact hl.elim
  | bar20 => rw [hs] at hl; exact hl.elim
  | tmemSt => rw [hs] at hl; exact hl.elim
  | tmemWait => rw [hs] at hl; exact hl.elim

/-! ### The assembly -/

/-- **`SmObligations` from the one premise about the launch.** -/
theorem smObligations_of_rest {Q : Params} {mem0 : Mem0} (hr : ScoreRest Q L mem0 g) :
    SmObligations Q L mem0 g where
  score hpre d hsc := stepAt_score hpre d hsc
  exit := exit_of_slack hr.rowSlack

end
end PTX.Kernels.InklingRelDecode.Proof.DComp
