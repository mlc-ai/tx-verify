-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.JR
public import Kernels.TmlFa4Fwd.Proof.CorrWarp.Fits
public import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
public import Kernels.TmlFa4Fwd.Proof.Correction.Shape
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Ideal
public import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Lag
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.SmWarp.Warp
public import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Start
public import Lemmas.Protocol.UnitItems
import Kernels.TmlFa4Fwd.Proof.Common.NoUb
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Export.ControlExit
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Src
import Kernels.TmlFa4Fwd.Proof.Epilogue.Facts
import Kernels.TmlFa4Fwd.Proof.Epilogue.Position
import Kernels.TmlFa4Fwd.Proof.Progress.CorrPre
import Kernels.TmlFa4Fwd.Proof.Common.FollowView
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Corr
import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Count
import Kernels.TmlFa4Fwd.Proof.Top.JRView
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Obj
import Lemmas.MBarrier.MBarrierInitOrder
import Lemmas.Protocol.GatedFaults
import Lemmas.Protocol.UnitReachBlocker
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # `ReadyArrive`: a ready barrier at an even phase has a correction lane before its arrival

A lane of warp 13 at its ready poll of stage `st` has a history of its ready barrier
(`readyObj`, initialized by the startup before the lane's CTA barrier), whose phase is at most 1
(`phase_le`: no correction lane arrives twice). At phase 0 some correction lane of the CTA has
made no arrival on it (`blocked`, the history being fault-free); that lane has not exited (its
exit comes after the arrival on the tile's path, and the CTA has a tile, as the output lane's
reference values say) and its state is at or before its arrival (`preReady`), with the first
pass's count of collectives (`corr_coll`). So `Progress.ReadyArrive` holds under the softmax
premises. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)
open PTX.MBarrier

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The correction sites by the ready barrier's arrival of stage `st`: a site whose state has not
passed it is at or before it, or on the path without a tile; the collectives' bound applies
outside the rounds and the tail. -/
theorem corr_sites_ready : ∀ st : Fin 2, Correction.allSites.all (fun s =>
    ((Correction.ptsOf (.arrive (208 + 8 * st.val))).countP (Correction.before s) != 0 ||
      Progress.preReady st s || s.noTile) &&
    (!Progress.preReady st s || Progress.Cr.round s || (Progress.Cr.tailOff s).isSome ||
      !Progress.Cr.late s)) = true := by
  decide

theorem corr_exit_pass (st : Fin 2) (l : Bool) (r : Nat) :
    Correction.passed (Correction.ptsOf (.arrive (208 + 8 * st.val))) (.exit l) r =
      if l then 1 else 0 := by
  have h : ∀ st : Fin 2, ∀ l : Bool,
      (Correction.ptsOf (.arrive (208 + 8 * st.val))).countP (Correction.before (.exit l)) =
        (if l then 1 else 0) ∧
      (Correction.ptsOf (.arrive (208 + 8 * st.val))).countP Correction.inRound = 0 := by
    decide
  simp only [Correction.passed, (h st l).1, (h st l).2, Nat.mul_zero, Nat.add_zero]

/-- A correction lane's arrivals of the class of the ready barrier's offset are arrivals on it. -/
theorem corr_cls_arr {y : Nat} {st : Fin 2} (hc : y / L.block = g / L.block) (es : List Event) :
    es.countP (cls L y (.corr (.arrive (208 + 8 * st.val)))) ≤
      Flow.arrivals (Epilogue.readyLoc L g st) es := by
  apply List.countP_mono_left
  intro e _ he'
  obtain ⟨pce, ke⟩ := e
  cases ke <;> simp only [cls, Correction.cls, decide_eq_true_eq, Bool.false_eq_true] at he'
  subst he'
  simp only [Flow.arrivesOn, sourceArrive, decide_eq_true_eq, Epilogue.readyLoc, Correction.bl, hc]

/-- A correction state's reference values on the path without a tile say the first pass picked
no tile. -/
theorem corr_noTile_noPicked {y : Nat} {d : Correction.D} {ns nv : Nat}
    (hF : CorrWarp.CFits p L y d ns nv) (hs : d.site.noTile = true) :
    ¬ ∃ R bal, Epilogue.Picked p L y R bal := by
  obtain ⟨rv, -, -, hFE, -⟩ := hF
  refine noPicked_exit hFE ?_
  obtain ⟨s, v, k⟩ := d
  cases s <;> simp_all [Correction.Site.noTile, CorrWarp.toE, CorrWarp.epi]
  all_goals (rename_i l; cases l <;> simp_all [Correction.Site.noTile])

/-- The JR of a role state of a lane of warps 8 to 11 is the correction warps'. -/
theorem jr_corr_role {y : Nat} {i : Role} {d : (frag p L y i).D} {n : Cls → Nat}
    (hJ : JR p L y (.inr ⟨i, d⟩, n))
    (hw : 8 ≤ Prologue.warpIndex L y ∧ Prologue.warpIndex L y ≤ 11) :
    ∃ dc, (⟨i, d⟩ : Σ i, (frag p L y i).D) = ⟨.correction, dc⟩ ∧
      CorrWarp.Ref p L (Prologue.warpIndex L y) y (.inr ⟨.correction, dc⟩, n) := by
  have h8 : ¬ Prologue.warpIndex L y < 8 := by omega
  simp only [JR_eq, h8, ite_false] at hJ
  unfold RefAll at hJ
  have h12 : Prologue.warpIndex L y ≠ 12 := by omega
  have h13 : Prologue.warpIndex L y ≠ 13 := by omega
  have h14 : ¬ (Prologue.warpIndex L y = 14 ∨ Prologue.warpIndex L y = 15) := by omega
  simp only [h12, h13, h14, ite_false] at hJ
  cases i with
  | correction => exact ⟨d, rfl, hJ⟩
  | _ => simp [CorrWarp.Ref] at hJ

set_option maxHeartbeats 4000000 in
/-- **A correction lane's machine dies only at its exit** (`CorrWarp.noUb`'s liveness). -/
theorem corr_live (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    {w y k : Nat} (hw8 : 8 ≤ w ∧ w ≤ 11) (hy : y < L.threads)
    (hw : Prologue.warpIndex L y = w) {σ : (thread p L y).D} {e : Event}
    (he : X.get (y, k) = some e) (hσ : Frame.stateAt (thread p L) X y k = some (some σ))
    (hR : CorrWarp.Ref p L w y σ) (hub : ∀ f, e.kind ≠ .ub f)
    (hn : (thread p L y).next σ e = none) : e.kind = .exit := by
  have hReads := cuQReadsFromLaunch hp hX
  have IH : ∀ n, CorrWarp.GoodUpTo p L w X n :=
    fun _ h j hin _ => CorrWarp.good hp hX hw8 hin.1 hin.2 j
  obtain ⟨σ, n⟩ := σ
  rcases σ with s | ⟨_ | _ | _ | _ | r | _, d⟩
  on_goal 7 => exact hR.elim
  · exact start_live hp hX he hσ hR.1 hn
  · exact hR.elim
  · exact hR.elim
  · obtain ⟨hJ, hF⟩ := hR (ub_zero hX he hσ)
    have hev := (CorrWarp.fired_both hp hX he hσ hub).1
    obtain ⟨hCE, hED⟩ := CorrWarp.cexpect hp hX hReads hy hw he hσ hJ hF hub fun _ => IH _
    exact CorrWarp.control_exit hp hy hF hCE hED hev hub (role_next_none hn)
  all_goals exact hR.elim

/-- The JR of any state of a lane of warps 8 to 11 is the correction warps' reference. -/
theorem jr_corrRef {y : Nat} {σ : (thread p L y).D} (hJ : JR p L y σ)
    (hw : 8 ≤ Prologue.warpIndex L y ∧ Prologue.warpIndex L y ≤ 11) :
    CorrWarp.Ref p L (Prologue.warpIndex L y) y σ := by
  have h8 : ¬ Prologue.warpIndex L y < 8 := by omega
  simp only [JR_eq, h8, ite_false] at hJ
  unfold RefAll at hJ
  have h12 : Prologue.warpIndex L y ≠ 12 := by omega
  have h13 : Prologue.warpIndex L y ≠ 13 := by omega
  have h14 : ¬ (Prologue.warpIndex L y = 14 ∨ Prologue.warpIndex L y = 15) := by omega
  simpa only [h12, h13, h14, ite_false] using hJ

set_option maxHeartbeats 4000000 in
theorem epi_exit {d : Epilogue.D} {pc : Nat} (hev : Epilogue.Ev p L g d ⟨pc, .exit⟩) :
    ∃ l, d.site = .exit l := by
  obtain ⟨s, rest⟩ := d
  cases s <;> simp only [Epilogue.Ev] at hev
  all_goals first | exact ⟨_, rfl⟩ | skip
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals simp_all [Epilogue.isStore]

set_option maxHeartbeats 4000000 in
/-- A correction exit event is fired at an exit site. -/
theorem corr_exit_site {s : Correction.Site} {v : Correction.V} {k : Fin 4} {pc : Nat}
    (hev : Correction.Ev p L g ⟨s, v, k⟩ ⟨pc, .exit⟩) : ∃ l, s = .exit l := by
  cases s <;> simp only [Correction.Ev] at hev
  all_goals first
    | exact ⟨_, rfl⟩
    | (exfalso; obtain ⟨l, hl⟩ := epi_exit hev; simp [Correction.Site.toE] at hl; done)
    | skip
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals simp_all [Correction.rdOrUb]

theorem readyLoc_off (L : Launch) (g : Nat) (st : Fin 2) :
    Epilogue.readyLoc L g st = obj L g (208 + 8 * st.val) ∧ ObjOff (208 + 8 * st.val) := by
  fin_cases st <;> exact ⟨rfl, by decide⟩

set_option maxHeartbeats 16000000 in
/-- **A ready barrier at an even phase has a correction lane before its arrival.** -/
theorem ready_arrive (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {st : Fin 2}
    (hg : g < L.threads) (hw : Prologue.warpIndex L g = 13) {d : Epilogue.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length =
      some (some (Epilogue.inj p L g d n)))
    (hs : d.site = .ready st) :
    ∃ before, stateBefore (X.objects (Epilogue.readyLoc L g st))
        (X.objects (Epilogue.readyLoc L g st)).length = some before ∧
      (before.phase % 2 = 0 → ∃ y, y < L.threads ∧ y / L.block = g / L.block ∧
        (¬ HasUb X → (∀ k pc, X.get (y, k) ≠ some ⟨pc, .exit⟩) ∧
          Progress.CorrPre p L st X y)) := by
  have hT := table_shape_of hp hFw
  have hF := table_followed hp hX hFw
  have hb512 := hp.block
  set mR := Epilogue.readyLoc L g st with hmR
  have O := readyObj hp hX hFw g st
  -- the output lane's reference values: the CTA has a tile, no successful poll of `mR` yet
  obtain ⟨R0, bal0, hC0, -⟩ : ∃ R bal, Epilogue.ChosenVals p L g R bal d (n .shfl) (n .vote) ∧
      True := by
    have hFE := (Epilogue.fits hp hX hg hw hσ).1
    simp only [Epilogue.Fits, hs] at hFE
    obtain ⟨R, bal, hC, -⟩ := hFE
    exact ⟨R, bal, hC, trivial⟩
  have hPick : Epilogue.Picked p L g R0 bal0 := hC0.1
  have hok : Flow.okPolls mR (X.tr g) = 0 := by
    have hcn := count hσ (.poll st)
    rw [List.take_length] at hcn
    have h0 : n (.poll st) = 0 := by
      rw [(Epilogue.fits hp hX hg hw hσ).2.2.2.2.2 st |>.1]
      simp [Epilogue.acqd, hs]
    simp only [Flow.okPolls]
    rw [← h0, ← hcn]
    rfl
  -- the history is not empty: the startup's initialization of `mR` is in it
  have hne : X.objects mR ≠ [] := by
    have hlen : 0 < (X.tr g).length := by
      by_contra h0
      rw [show (X.tr g).length = 0 by omega, Frame.stateAt_zero] at hσ
      simp [thread, glued, Code.glue, Code.counted, Code.enter, Startup.code, exit] at hσ
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[(X.tr g).length - 1]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hσ' : Frame.stateAt (thread p L) X g ((X.tr g).length - 1 + 1) =
        some (some (.inr ⟨.epilogue, d⟩, n)) := by
      rw [show (X.tr g).length - 1 + 1 = (X.tr g).length by omega]; exact hσ
    obtain ⟨⟨i, dr⟩, n0, hσ0⟩ := epi_prev he hσ' (by rw [hs]; simp)
    have hb := role_bar0 hp hX _ hσ0
    obtain ⟨hloc, hoff⟩ := readyLoc_off L g st
    obtain ⟨j, c, hinit, -⟩ := init_exists hp hX hT hF hg (by omega) hb hoff
    rw [← hloc] at hinit
    obtain ⟨i, r, hi, -⟩ := init_record_of_consistent hX hinit
    intro h0
    rw [h0] at hi
    simp at hi
  obtain ⟨before, hst⟩ := PTX.MbarRing.Unit.final_of_init hX O.init O.noInval hne
  refine ⟨before, hst, fun hph => ?_⟩
  -- no correction lane arrives twice: the uses of the counted arrivals are 0
  have huse : ∀ x ∈ PTX.MbarRing.Unit.S X mR (corrLane L (g / L.block)), x.2 = 0 := by
    intro x hx
    simp only [PTX.MbarRing.Unit.S, Finset.mem_filter] at hx
    obtain ⟨-, r, hr, hid, -, ha⟩ := hx
    cases O.src r hr with
    | init ha' => rw [ha] at ha'; cases ha'
    | poll _ _ ha' => rw [ha] at ha'; cases ha'
    | @arrive g' j' pc' sc' hid' hg' he' ha' =>
      rw [hid] at hid'
      simp only [AsyncCopy.Ref.thread.injEq] at hid'
      rw [← hid'] at he'
      simp only [PTX.MbarRing.Unit.it] at he'
      have h1 := (nthEv_spec_of_get he').2
      have h2 := ready_arr_zero (g := g) (st := st) hp hX hFw he'
        (by simp [Flow.arrivesOn, sourceArrive, hmR])
      rw [← hmR] at h2
      simp only [Flow.arrivals] at h2
      omega
  have hR : PTX.MbarRing.Unit.Reach L kernel Assumptions.all X mR 128 (corrLane L (g / L.block))
      0 g := fun x hx j hj => absurd hj (by rw [huse x hx]; omega)
  have hle := O.phase_le hX hR hst (Nat.zero_le _)
  rw [hok] at hle
  have hph0 : before.phase = 0 := by omega
  -- a short producer
  have hgate : PTX.MbarRing.Unit.Gated L kernel Assumptions.all X mR 128
      (corrLane L (g / L.block)) 0 := by
    intro a i pc sc he hpos
    have := ready_arr_zero (g := g) (st := st) hp hX hFw he
      (by simp [Flow.arrivesOn, sourceArrive, hmR])
    rw [← hmR] at this
    omega
  have hff := O.fault_free hX hgate
  obtain ⟨a, ha⟩ := O.blocked hX hst
  rw [hph0] at ha
  have harr := (PTX.MbarRing.Unit.arrivals_le_unitRec hX hff (corrLane L (g / L.block) a)).trans ha
  set y := corrLane L (g / L.block) a with hy
  have hyc : y / L.block = g / L.block := by
    simp only [hy, corrLane]; rw [hb512]; omega
  have hyt : y < L.threads := by
    have h1 : g / L.block < L.grid := (Nat.div_lt_iff_lt_mul (by omega)).2 hg
    simp only [hy, corrLane]
    show _ < L.grid * L.block
    rw [hb512] at h1 ⊢
    have : (g / 512 + 1) * 512 ≤ L.grid * 512 := Nat.mul_le_mul_right _ h1
    omega
  have hyw : 8 ≤ Prologue.warpIndex L y ∧ Prologue.warpIndex L y ≤ 11 := by
    simp only [Prologue.warpIndex, hy, corrLane, hb512]
    omega
  -- the correction lane's arrivals of the class are none
  have hcls0 : ∀ k, ((X.tr y).take k).countP (cls L y (.corr (.arrive (208 + 8 * st.val)))) = 0 :=
    fun k => by
      have h1 := corr_cls_arr (st := st) hyc ((X.tr y).take k)
      have h2 : Flow.arrivals mR ((X.tr y).take k) ≤ Flow.arrivals mR (X.tr y) :=
        (List.take_sublist _ _).countP_le
      simp only [hmR] at h1 h2 harr
      omega
  refine ⟨y, hyt, hyc, fun hub => ?_⟩
  have hnex : ∀ k pc, X.get (y, k) ≠ some ⟨pc, .exit⟩ := by
    intro k pc hx
    -- an exit of the lane is after its arrival on the tile's path
    obtain ⟨⟨σ1, n1⟩, hσ1, hJ1, hi1, hev1⟩ := Frame.RoleTable.ev_of_ne_ubU (T := table p L)
      (S := fun g => g < L.threads) (fun g hg => thread_sound hp hg) hX hT hF hyt hx
      (fun f hf => by cases hf)
    rcases σ1 with s1 | ⟨i1, d1⟩
    · have hEv : Startup.Ev L y s1 ⟨pc, .exit⟩ := hev1
      obtain ⟨site, x1, x2, x3⟩ := s1
      cases site with
      | enter r => exact jr_start_site hJ1 r rfl
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
    obtain ⟨dc, hdc, hRc⟩ := jr_corr_role hJ1 hyw
    obtain ⟨rfl, hd1⟩ := Sigma.mk.inj_iff.mp hdc
    have hd1 := eq_of_heq hd1
    subst hd1
    obtain ⟨⟨⟨r1, ℓ1, hQ⟩, -⟩, hFc⟩ := hRc (ub_zero hX hx hσ1)
    have hEv : Correction.Ev p L y d1 ⟨pc, .exit⟩ :=
      hev1.1.data_or_vote.resolve_right (by rintro ⟨_,_,hv⟩; cases hv)
    obtain ⟨s1, v1, k1⟩ := d1
    have hsx : ∃ l, s1 = .exit l := corr_exit_site hEv
    obtain ⟨l, rfl⟩ := hsx
    have hcnt := hQ.cnt (.arrive (208 + 8 * st.val)) (by simp)
    simp only [CorrWarp.rc, Correction.Control.D.scheduler, corr_exit_pass] at hcnt
    have hcl := count hσ1 (.corr (.arrive (208 + 8 * st.val)))
    rw [hcls0] at hcl
    cases l
    · exact corr_noTile_noPicked hFc rfl ⟨R0, bal0, Epilogue.Picked.cta hyc.symm hPick⟩
    · simp at hcnt; omega
  refine ⟨hnex, ?_⟩
  · -- the lane's state at the end of its trace
    have hfol := hF y hyt (X.tr y).length
    cases hσy : Frame.stateAt (thread p L) X y (X.tr y).length with
    | none =>
      exfalso
      have htr : Frame.Tracked (thread p L) X := fun g k hg => (hF g hg k).1
      obtain ⟨i, σi, hi, hσi, hσi1⟩ := Frame.first_stop htr hyt hσy
      have hilt : i < (X.tr y).length := by
        by_contra hge
        rw [Frame.stateAt_of_le (show (X.tr y).length ≤ i by omega), hσy] at hσi
        cases hσi
      obtain ⟨e, he⟩ : ∃ e, (X.tr y)[i]? = some e := ⟨_, List.getElem?_eq_getElem hilt⟩
      rw [Frame.stateAt_succ he, hσi] at hσi1
      have hJi := (hF y hyt i).2 σi hσi
      have hRi := jr_corrRef hJi hyw
      have hge : X.get (y, i) = some e := he
      have hube : ∀ f, e.kind ≠ .ub f := fun f hf =>
        hub ⟨(y, i), e.pc, f, by rw [hge, ← hf]⟩
      have hk := corr_live hp hX hyw hyt rfl hge hσi hRi hube (by
        simpa [Code.toMachine] using hσi1)
      obtain ⟨pce, ke⟩ := e
      simp only at hk
      subst hk
      exact hnex i pce hge
    | some o =>
      cases o with
      | none => exact absurd hσy hfol.1
      | some σ =>
        have hJy := hfol.2 σ hσy
        obtain ⟨σ1, n1⟩ := σ
        rcases σ1 with s1 | ⟨i1, d1⟩
        · exact .inl ⟨s1, n1, hσy, fun r => jr_start_site hJy r⟩
        obtain ⟨dc, hdc, hRc⟩ := jr_corr_role hJy hyw
        obtain ⟨rfl, hd1⟩ := Sigma.mk.inj_iff.mp hdc
        have hd1 := eq_of_heq hd1
        subst hd1
        have hub1 : n1 .ub = 0 := by
          have := count hσy .ub
          rw [List.take_length] at this
          rw [← this, List.countP_eq_zero]
          intro e he' hue
          obtain ⟨pc, ke⟩ := e
          cases ke <;> simp [cls] at hue
          rename_i f
          obtain ⟨kk, hkk⟩ := List.mem_iff_getElem?.mp he'
          exact hub ⟨(y, kk), pc, f, hkk⟩
        obtain ⟨⟨⟨r1, ℓ1, hQ⟩, -⟩, hFc⟩ := hRc hub1
        have hcnt := hQ.cnt (.arrive (208 + 8 * st.val)) (by simp)
        have hcl := count hσy (.corr (.arrive (208 + 8 * st.val)))
        rw [hcls0] at hcl
        simp only [CorrWarp.rc] at hcnt
        rw [← hcl] at hcnt
        have hsite := List.all_eq_true.mp (corr_sites_ready st) d1.site
          (Correction.mem_allSites _)
        simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at hsite
        obtain ⟨h1, h2⟩ := hsite
        have hpass : (Correction.ptsOf (.arrive (208 + 8 * st.val))).countP
            (Correction.before d1.site) = 0 := by
          simp only [Correction.passed, Correction.Control.D.scheduler] at hcnt
          omega
        rcases h1 with (h1 | h1) | h1
        · exact absurd hpass h1
        · refine .inr ⟨d1, n1, hσy, h1, fun hr ht => ?_⟩
          have hl : Progress.Cr.late d1.site = false := by
            rcases h2 with ((h2 | h2) | h2) | h2
            · simp [h1] at h2
            · simp [hr] at h2
            · simp [ht] at h2
            · simpa using h2
          exact Progress.corr_coll hp (hRc) hub1 hr ht hl
        · exact absurd ⟨R0, bal0, Epilogue.Picked.cta hyc.symm hPick⟩ (corr_noTile_noPicked hFc h1)

/-- **`Progress.ReadyArrive`**, under the softmax premises of `Top.correct2`. -/
theorem readyArrive (hp : Pre p L m) :
    Progress.ReadyArrive p L m :=
  fun _ hX _ _ hg hw _ _ hσ hs =>
    ready_arrive hp hX (follow hp hX) hg hw hσ hs

end
end PTX.Kernels.TmlFa4Fwd.Proof
