-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Places
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Lib.OutputSlots
public import Kernels.TmlFa4Fwd.Proof.Common.Sound
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Facts
import Kernels.TmlFa4Fwd.Proof.Softmax.Fragment
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InitOne
public import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Start
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Use
import Kernels.TmlFa4Fwd.Proof.Correction.Export.Count
public import Kernels.TmlFa4Fwd.Proof.Top.Table
public import Lemmas.Execution.ControlProjection
public import Lemmas.Kernel.Safety.Classes
public import Lemmas.Kernel.Safety.StateInv
public import Lemmas.Protocol.GatedFaults
public import Lemmas.Protocol.UnitObject
public import Lemmas.Protocol.UnitReachBlocker
import Kernels.TmlFa4Fwd.Proof.Lib.Prev
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Count
import Lemmas.Protocol.ObjectSource
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Proof.Top.JRView

@[expose] public section

/-! # The ready barriers' history

The output warp's ready barrier of stage `st` (shared offset `208 + 8 st`, count 128) is named
only by the output warp's ready polls and the correction lanes' arrivals (`ready_use'`). No event
invalidates an object (`no_inval`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### No invalidation -/

set_option hygiene false in
/-- Split a shape hypothesis on an invalidation into its cases and close them. -/
macro "noinval_close" : tactic => `(tactic| (
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (try simp_all [Epilogue.isStore, Correction.rdOrUb, Softmax.rdOrUb,
    Softmax.tcLdOrUb])))

set_option maxHeartbeats 4000000 in
theorem epi_noinval {d : Epilogue.D} {pc : Nat} {l : Loc}
    (hev : Epilogue.Ev p L g d ⟨pc, .mbInval l⟩) : False := by
  obtain ⟨s, rest⟩ := d
  cases s <;> simp only [Epilogue.Ev] at hev
  noinval_close

set_option maxHeartbeats 4000000 in
theorem corr_noinval {d : Correction.D} {pc : Nat} {l : Loc}
    (hev : Correction.Ev p L g d ⟨pc, .mbInval l⟩) : False := by
  obtain ⟨s, v, k⟩ := d
  cases s <;> simp only [Correction.Ev] at hev
  all_goals first | exact epi_noinval hev | skip
  noinval_close

set_option maxHeartbeats 4000000 in
theorem soft_noinval {d : Softmax.D} {pc : Nat} {l : Loc}
    (hev : Softmax.Ev p L g d ⟨pc, .mbInval l⟩) : False := by
  obtain ⟨s, v, k, acc⟩ := d
  cases s <;> simp only [Softmax.Ev] at hev
  all_goals first | exact epi_noinval hev | skip
  noinval_close

set_option maxHeartbeats 4000000 in
theorem mma_noinval {d : Mma.D} {pc : Nat} {l : Loc}
    (hev : Mma.Ev p L g d ⟨pc, .mbInval l⟩) : False := by
  obtain ⟨s, rest⟩ := d
  cases s <;> simp only [Mma.Ev] at hev
  all_goals first | exact epi_noinval hev | skip
  noinval_close

set_option maxHeartbeats 4000000 in
theorem ld_noinval {w : Nat} {d : Loader.D} {pc : Nat} {l : Loc}
    (hev : Loader.Ev p L g w d ⟨pc, .mbInval l⟩) : False := by
  obtain ⟨s, rest⟩ := d
  cases s <;> simp only [Loader.Ev] at hev
  all_goals first | exact epi_noinval hev | skip
  noinval_close

set_option maxHeartbeats 4000000 in
/-- **No event invalidates an mbarrier.** -/
theorem no_inval (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) :
    ∀ e l, ¬ X.MbInval e l := by
  rintro ⟨h, k⟩ l ⟨pc, he⟩
  have hT := table_shape_of hp hFw
  have hF := table_followed hp hX hFw
  have hh := Frame.lt_of_get hX he
  obtain ⟨⟨σ1, n⟩, hσ, hJ, hi, hev⟩ := Frame.RoleTable.ev_of_ne_ubU (T := table p L)
    (S := fun g => g < L.threads) (fun g hg => thread_sound hp hg) hX hT hF hh he
    (fun f hf => by cases hf)
  have hJ' : JR p L h (σ1, n) := hJ
  rcases σ1 with s | ⟨i, d⟩
  · have hEv : Startup.Ev L h s ⟨pc, .mbInval l⟩ := hev
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site with
    | enter r => exact jr_start_site hJ' r rfl
    | sh j =>
      fin_cases j <;> simp only [Startup.Ev] at hEv <;> obtain ⟨_, _, hk⟩ := hEv <;> cases hk
    | fence => simp only [Startup.Ev] at hEv; cases hEv
    | bar => simp only [Startup.Ev] at hEv; cases hEv
    | elect j =>
      simp only [Startup.Ev] at hEv
      rcases hEv with ⟨_, _, -, hk⟩ | ⟨_, hk⟩ <;> cases hk
    | init q =>
      simp only [Startup.Ev] at hEv
      rcases hEv with ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk
  cases i with
  | epilogue => exact epi_noinval hev
  | correction => exact corr_noinval (hev.1.data_or_vote.resolve_right (by rintro ⟨_,_,h⟩; cases h))
  | softmax => exact soft_noinval hev.1
  | loader b => exact ld_noinval hev
  | mma =>
    rcases d with s | ⟨_, d⟩
    · rcases hev with ⟨_, _, _, hk⟩ | ⟨_, _, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk
    · exact mma_noinval hev
  | stub r =>
    simp only [JR_eq] at hJ'
    split_ifs at hJ'
    · exact hJ'
    · unfold RefAll at hJ'
      split_ifs at hJ' <;> simp_all [Mma.Ref, Epilogue.Ref, LdWarp.Ref, CorrWarp.Ref]

/-! ### The ready barrier as a unit object -/

/-- The correction lanes of CTA `c`: lanes 256 to 383. -/
def corrLane (L : Launch) (c : Nat) (a : Fin 128) : Nat := c * L.block + 256 + a.val

theorem corrLane_inj (L : Launch) (c : Nat) : Function.Injective (corrLane L c) := by
  intro a b h
  simp only [corrLane] at h
  exact Fin.ext (by omega)

/-- A correction state's lane is of warps 8 to 11. -/
theorem jr_corr {h : Nat} {d : Correction.Control.D} {n : Cls → Nat}
    (hJ : JR p L h (.inr ⟨.correction, d⟩, n)) (hw16 : Prologue.warpIndex L h < 16) :
    8 ≤ Prologue.warpIndex L h ∧ Prologue.warpIndex L h ≤ 11 := by
  simp only [JR_eq] at hJ
  split_ifs at hJ with h8
  · exact hJ.elim
  · unfold RefAll at hJ
    split_ifs at hJ <;> simp_all [Mma.Ref, Epilogue.Ref, LdWarp.Ref]; omega

/-- A correction lane of CTA `c` is `corrLane L c a` for some `a`. -/
theorem corrLane_of (hp : Pre p L m) {h c : Nat} (hc : h / L.block = c)
    (hw : 8 ≤ Prologue.warpIndex L h ∧ Prologue.warpIndex L h ≤ 11) :
    ∃ a, h = corrLane L c a := by
  have hb := hp.block
  simp only [Prologue.warpIndex, hb] at hw
  refine ⟨⟨h % L.block - 256, by rw [hb]; omega⟩, ?_⟩
  have := Nat.div_add_mod h L.block
  rw [hc] at this
  simp only [corrLane]
  rw [hb] at this ⊢
  omega

/-- **Who names a ready barrier**: an event that names the ready barrier of stage `st` of lane
`g`'s CTA and is no initialization is of a lane of that CTA, either the output warp's parity-0 poll
before any successful one, or a correction lane's unit release arrival. -/
theorem ready_use' (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {h k : Nat} {e : Event}
    {st : Fin 2} (he : X.get (h, k) = some e) (hm : MbarOf e (Epilogue.readyLoc L g st))
    (hni : ∀ c, e.kind ≠ .mbInit (Epilogue.readyLoc L g st) c) :
    h < L.threads ∧ h / L.block = g / L.block ∧
      ((∃ ok, e.kind = .wait (Epilogue.readyLoc L g st) 0 ok true .cta ∧
          Prologue.warpIndex L h = 13 ∧
          okPolls (Epilogue.readyLoc L g st) ((X.tr h).take k) = 0) ∨
        e.kind = .arrive (Epilogue.readyLoc L g st) 0 1 true .cta ∧
          8 ≤ Prologue.warpIndex L h ∧ Prologue.warpIndex L h ≤ 11) := by
  obtain ⟨hc, hu⟩ := bar_use (o := 208 + 8 * st.val) hp hX hFw he hm hni
  refine ⟨Frame.lt_of_get hX he, hc, ?_⟩
  cases hu with
  | epiPoll st' ok hw _ hk h0 => exact .inl ⟨ok, hk, hw, h0⟩
  | corrArr hw _ hk => exact .inr ⟨hk, hw⟩
  | epiArr _ _ ho | corrPoll _ _ ho => omega
  | softArr _ _ _ ho | softPoll _ _ _ _ ho | ldAsync _ ho => omega
  | mmaPoll _ _ ho => unfold MmaPollOff at ho; omega
  | mmaCommit _ _ ho => unfold MmaCommitOff at ho; omega
  | ldPoll _ _ _ ho => unfold LdPollOff at ho; omega
  | ldArr _ _ ho | ldCopy _ _ _ ho => unfold LdTmaOff at ho; omega

theorem readyLoc_obj (L : Launch) (g : Nat) (st : Fin 2) :
    Epilogue.readyLoc L g st = obj L g (initOff ⟨26 + st.val, by omega⟩) ∧
      initCnt ⟨26 + st.val, by omega⟩ = 128 := by
  fin_cases st <;> exact ⟨rfl, rfl⟩

theorem readyLoc_cta {h : Nat} (hc : h / L.block = g / L.block) (st : Fin 2) :
    Epilogue.readyLoc L h st = Epilogue.readyLoc L g st := by
  simp only [Epilogue.readyLoc, hc]

set_option maxHeartbeats 8000000 in
/-- **The ready barrier of stage `st` is a unit object** of the CTA's 128 correction lanes,
polled with offset 0. -/
theorem readyObj (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (g : Nat) (st : Fin 2) :
    PTX.MbarRing.Unit.Obj X (Epilogue.readyLoc L g st) 128 (corrLane L (g / L.block)) 0 := by
  have hU := fun {h k} {e : Event} (he : X.get (h, k) = some e)
      (hm : MbarOf e (Epilogue.readyLoc L g st))
      (hni : ∀ c, e.kind ≠ .mbInit (Epilogue.readyLoc L g st) c) =>
    ready_use' hp hX hFw he hm hni
  obtain ⟨hloc, hcnt⟩ := readyLoc_obj L g st
  refine ⟨by decide, corrLane_inj L _, fun r hr => ?_, ?_, ?_, fun {h k pc par acq sc} he => ?_,
    by decide⟩
  · cases AsyncCopy.record_source hX.tma.2.2.1 hr with
    | init hid he ha => exact .init ha
    | wait hid he ha => exact .poll hid he ha
    | @arrive g' j pc tx c rel sc hid he ha =>
      rcases hU he rfl (fun _ h => by cases h) with ⟨-, hc, ⟨_, hk, _⟩ | ⟨hk, hw⟩⟩
      · cases hk
      · simp only [Kind.arrive.injEq] at hk
        obtain ⟨-, rfl, rfl, rfl, rfl⟩ := hk
        obtain ⟨a, ha'⟩ := corrLane_of hp hc hw
        exact .arrive hid ⟨a, ha'⟩ he ha
    | inval hid he ha => exact absurd ⟨_, he⟩ (no_inval hp hX hFw _ _)
    | increment hid he ha =>
      rcases hU he rfl (fun _ h => by cases h) with ⟨-, -, ⟨_, hk, _⟩ | ⟨hk, _⟩⟩ <;> cases hk
    | tensor hid he hm ha =>
      rcases hU he hm (fun _ h => by cases h) with ⟨-, -, ⟨_, hk, _⟩ | ⟨hk, _⟩⟩ <;> cases hk
    | arriveOn hid he hm hn ha =>
      rcases hU he hm.symm (fun _ h => by cases h) with ⟨-, -, ⟨_, hk, _⟩ | ⟨hk, _⟩⟩ <;> cases hk
    | bulk hid he hc hn ha =>
      rcases hU he hc (fun _ h => by cases h) with ⟨-, -, ⟨_, hk, _⟩ | ⟨hk, _⟩⟩ <;> cases hk
    | commit hid he ht ha =>
      rcases hU he ⟨_, ht⟩ (fun _ h => by cases h) with ⟨-, -, ⟨_, hk, _⟩ | ⟨hk, _⟩⟩ <;> cases hk
    | clc hid he hm htg ha =>
      rcases hU he ⟨_, htg, hm⟩ (fun _ h => by cases h) with
        ⟨-, -, ⟨_, hk, _⟩ | ⟨hk, _⟩⟩ <;> cases hk
  · rw [hloc, ← hcnt]
    exact obj_initFirst hp hX hFw g _
  · exact AsyncCopy.objects_noInval hX.tma.2.2.1 (no_inval hp hX hFw) _
  · rcases hU he rfl (fun _ h => by cases h) with ⟨-, -, ⟨_, hk, -, h0⟩ | ⟨hk, _⟩⟩
    · simp only [Kind.wait.injEq] at hk
      obtain ⟨-, rfl, -, -, -⟩ := hk
      rw [h0]
    · cases hk

/-! ### One arrival per correction lane -/

/-- **A correction lane arrives on a ready barrier once**: before any arrival of a lane on the
ready barrier of stage `st`, the lane has made none. -/
theorem ready_arr_zero (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {y i : Nat} {ev : Event}
    {st : Fin 2} (he : X.get (y, i) = some ev)
    (ha : Flow.arrivesOn (Epilogue.readyLoc L g st) ev = true) :
    Flow.arrivals (Epilogue.readyLoc L g st) ((X.tr y).take i) = 0 := by
  obtain ⟨pc, kind⟩ := ev
  have hm : MbarOf ⟨pc, kind⟩ (Epilogue.readyLoc L g st) := by
    cases kind <;> simp_all [Flow.arrivesOn, sourceArrive, MbarOf]
  have hni : ∀ c, kind ≠ .mbInit (Epilogue.readyLoc L g st) c := by
    intro c h; subst h; simp [Flow.arrivesOn, sourceArrive] at ha
  rcases ready_use' hp hX hFw he hm hni with ⟨-, hc, ⟨_, hk, _⟩ | ⟨hk, hw⟩⟩
  · simp only at hk
    subst hk
    simp [Flow.arrivesOn, sourceArrive] at ha
  · simp only at hk
    subst hk
    rw [← readyLoc_cta hc] at he ⊢
    exact corr_ready_arr hp hX hFw hw.1 hw.2 st he

/-- **The step into an output state other than its first**: the previous state is a role
state. -/
theorem epi_prev {h k : Nat} {e : Event} {d : Epilogue.D} {n : Cls → Nat}
    (he : (X.tr h)[k]? = some e)
    (hσ : Frame.stateAt (thread p L) X h (k + 1) = some (some (.inr ⟨.epilogue, d⟩, n)))
    (hs : d.site ≠ .start) :
    ∃ r n0, Frame.stateAt (thread p L) X h k = some (some (.inr r, n0)) := by
  refine prev_role (i := .epilogue) he hσ (fun hd => ?_)
  exact hs (by rw [hd])

end
end PTX.Kernels.TmlFa4Fwd.Proof
