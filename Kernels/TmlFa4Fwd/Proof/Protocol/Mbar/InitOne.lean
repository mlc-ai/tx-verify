-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Kernel.FrameU

public import Kernels.TmlFa4Fwd.Proof.SmWarp.Export.Follow
public import Kernels.TmlFa4Fwd.Proof.Common.Sound
public import Kernels.TmlFa4Fwd.Proof.Lib.InitFirst
import Kernels.TmlFa4Fwd.Proof.Softmax.Fragment
public import Kernels.TmlFa4Fwd.Proof.Protocol.Bar.Count
public import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
public import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Start
import Kernels.TmlFa4Fwd.Proof.Top.Register
public import Lemmas.CtaBarrier.CtaBarrierFault
public import Lemmas.Execution.ControlProjection
public import Lemmas.Kernel.Safety.Classes
public import Lemmas.Kernel.Source.WarpColl
public import Lemmas.Kernel.UbLast
public import Lemmas.Protocol.ObjectSource
public import Lemmas.Protocol.PairTmaRing.Hyp
import Lemmas.Kernel.ElectSource
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Kernels.TmlFa4Fwd.Proof.Top.JRView

@[expose] public section

/-! # Each object is initialized once, with its count

Every `mbarrier.init` event of a lane is the startup's, at initialization site `q` of a lane of
warp 0 that won an election before it (`init_event`); the lanes of warp 0 of a CTA that won an
election are one lane (`elect_winner`), whose sites are the path's (`lead_path`), so it
initializes each object at one position (`initPos q`) with the count `initCnt q`
(`init_unique`). With the publication of the initialization (`use_pub`), every object of a CTA
is initialized first (`obj_initFirst`, `PairTmaRing.InitFirst`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### No role initializes an object -/

set_option hygiene false in
/-- Split a shape hypothesis on an initialization event into its cases and close them. -/
macro "noinit_close" : tactic => `(tactic| (
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (try simp_all [Epilogue.isStore])))

set_option maxHeartbeats 4000000 in
theorem epi_noinit {d : Epilogue.D} {pc c : Nat} {l : Loc}
    (hev : Epilogue.Ev p L g d ⟨pc, .mbInit l c⟩) : False := by
  obtain ⟨s, rest⟩ := d
  cases s <;> simp only [Epilogue.Ev] at hev
  noinit_close

set_option maxHeartbeats 4000000 in
theorem corr_noinit {d : Correction.D} {pc c : Nat} {l : Loc}
    (hev : Correction.Ev p L g d ⟨pc, .mbInit l c⟩) : False := by
  obtain ⟨s, v, k⟩ := d
  cases s <;> simp only [Correction.Ev] at hev
  all_goals first | exact epi_noinit hev | skip
  noinit_close
  all_goals simp_all [Correction.rdOrUb]

set_option maxHeartbeats 4000000 in
theorem soft_noinit {d : Softmax.D} {pc c : Nat} {l : Loc}
    (hev : Softmax.Ev p L g d ⟨pc, .mbInit l c⟩) : False := by
  obtain ⟨s, v, k, acc⟩ := d
  cases s <;> simp only [Softmax.Ev] at hev
  all_goals first | exact epi_noinit hev | skip
  noinit_close
  all_goals simp_all [Softmax.rdOrUb, Softmax.tcLdOrUb]

set_option maxHeartbeats 4000000 in
theorem mma_noinit {d : Mma.D} {pc c : Nat} {l : Loc}
    (hev : Mma.Ev p L g d ⟨pc, .mbInit l c⟩) : False := by
  obtain ⟨s, rest⟩ := d
  cases s <;> simp only [Mma.Ev] at hev
  all_goals first | exact epi_noinit hev | skip
  noinit_close

set_option maxHeartbeats 4000000 in
theorem ld_noinit {w : Nat} {d : Loader.D} {pc c : Nat} {l : Loc}
    (hev : Loader.Ev p L g w d ⟨pc, .mbInit l c⟩) : False := by
  obtain ⟨s, rest⟩ := d
  cases s <;> simp only [Loader.Ev] at hev
  all_goals first | exact epi_noinit hev | skip
  noinit_close

/-! ### The startup's initializations -/

/-- A startup state of a lane's reference invariant at an initialization site is of warp 0. -/
theorem jr_init {s : Startup.D} {n : Cls → Nat} (hJ : JR p L g (.inl s, n)) {q : Fin 34}
    (hs : s.site = .init q) : Prologue.warpIndex L g = 0 ∧ StartAt0 L s n := by
  obtain ⟨site, x1, x2, x3⟩ := s
  simp only at hs
  subst hs
  rw [JR_eq] at hJ
  split_ifs at hJ
  · simp only [SmWarp.Ref, SmWarp.StartW] at hJ
    split_ifs at hJ with h0
    · exact ⟨h0, hJ.1⟩
    · simp [StartAt] at hJ
  · unfold RefAll at hJ
    split_ifs at hJ <;>
      simp [Mma.Ref, Epilogue.Ref, LdWarp.Ref, CorrWarp.Ref, StartAt] at hJ

/-- The site after an election's block is no initialization. -/
theorem afterBlock_notInit (d : Startup.D) (j : Fin 16) (q : Fin 34) :
    (Startup.afterBlock d j).site ≠ .init q := by
  unfold Startup.afterBlock
  split <;> fin_cases j <;> simp [Startup.nonzeroSite, Startup.afterSite]

/-- **A lane at an initialization site has won an election before it**: its trace has an
election, with the full mask, that returned the lane's own index. -/
theorem init_won (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {h : Nat} :
    ∀ k {s : Startup.D} {n : Cls → Nat},
      Frame.stateAt (thread p L) X h k = some (some (.inl s, n)) → (∃ q, s.site = .init q) →
      ∃ j < k, ∃ pc inst, X.get (h, j) = some ⟨pc, .elect (2 ^ 32 - 1) inst (laneOf L h)⟩ := by
  intro k
  induction k with
  | zero =>
    intro s n hσ ⟨q, hq⟩
    rw [Frame.stateAt_zero] at hσ
    have h2 := Option.some.inj (Option.some.inj hσ)
    simp only [thread, glued, Code.glue, Code.counted, Startup.code, Prod.mk.injEq,
      Sum.inl.injEq] at h2
    simp only [Code.enter, exit, Sum.inl.injEq] at h2
    rw [← h2.1] at hq
    simp at hq
  | succ k ih =>
    intro s n hσ hq
    by_cases hk : k < (X.tr h).length
    swap
    · rw [Frame.stateAt_of_le (show (X.tr h).length ≤ k + 1 by omega),
        ← Frame.stateAt_of_le (show (X.tr h).length ≤ k by omega)] at hσ
      obtain ⟨j, hj, pc, inst, he⟩ := ih hσ hq
      exact ⟨j, by omega, pc, inst, he⟩
    obtain ⟨e, he⟩ : ∃ e, (X.tr h)[k]? = some e := ⟨_, List.getElem?_eq_getElem hk⟩
    rw [Frame.stateAt_succ he] at hσ
    cases hσ0 : Frame.stateAt (thread p L) X h k with
    | none => rw [hσ0] at hσ; simp at hσ
    | some o =>
      cases o with
      | none => rw [hσ0] at hσ; simp [Code.toMachine] at hσ
      | some σ =>
        rw [hσ0] at hσ
        obtain ⟨σ0, n0⟩ := σ
        change (thread p L h).next (σ0, n0) e = some (some (.inl s, n)) at hσ
        obtain ⟨h1, -⟩ := Code.counted_next_some (C := glued p L h) hσ
        rcases σ0 with s0 | ⟨i0, d0⟩
        swap
        · simp only [glued, Code.glue] at h1
          cases hr : (frag p L h i0).next d0 e with
          | none => rw [hr] at h1; simp at h1
          | some o' =>
            cases o' with
            | none => rw [hr] at h1; simp at h1
            | some d1 => rw [hr] at h1; simp at h1
        simp only [glued, Code.glue] at h1
        cases hs : Startup.succ L h s0 e with
        | none => simp [Startup.code, hs] at h1
        | some o' =>
          cases o' with
          | none => simp [Startup.code, hs] at h1
          | some s' =>
            simp only [Startup.code, hs, Option.map_some, Option.some.injEq] at h1
            have hss : s' = s := by
              unfold Code.enter at h1
              split at h1
              · simp at h1
              · simpa using h1
            subst hss
            obtain ⟨q, hq⟩ := hq
            have hge : X.get (h, k) = some e := he
            obtain ⟨site, x1, x2, x3⟩ := s0
            cases site with
            | init q0 =>
              obtain ⟨j, hj, pc, inst, hj'⟩ := ih hσ0 ⟨q0, rfl⟩
              exact ⟨j, by omega, pc, inst, hj'⟩
            | elect j =>
              have hE := (start_fired hp hX hge hσ0).1
              simp only [Startup.Ev] at hE
              obtain ⟨pc, kind⟩ := e
              rcases hE with ⟨inst, ld, -, hk2⟩ | ⟨f, hk2⟩
              swap
              · simp only at hk2; subst hk2; simp [Startup.succ] at hs
              simp only at hk2
              subst hk2
              simp only [Startup.succ, Option.some.injEq] at hs
              subst hs
              split at hq
              · rename_i hld
                exact ⟨k, by omega, pc, inst, by rw [hge, hld]⟩
              · exact absurd hq (afterBlock_notInit _ _ _)
            | sh jj =>
              simp only [Startup.succ] at hs
              split at hs
              · simp only [Startup.word32] at hs
                split at hs
                · simp only [Option.some.injEq] at hs
                  subst hs
                  fin_cases jj <;> simp at hq
                  split_ifs at hq <;> simp at hq
                · simp at hs
              · simp at hs
            | fence =>
              simp only [Startup.succ, Option.some.injEq] at hs
              subst hs
              simp at hq
            | bar =>
              simp only [Startup.succ, Option.some.injEq] at hs
              subst hs
              unfold Startup.enterOf at hq
              split_ifs at hq <;> simp at hq
            | enter r => simp [Startup.succ] at hs

/-- The step of a startup state to a startup state: the previous state is a startup state, and
the successor is the startup's own (no role entered). -/
theorem start_prev {h k : Nat} {e : Event} {s : Startup.D} {n : Cls → Nat}
    (he : (X.tr h)[k]? = some e)
    (hσ : Frame.stateAt (thread p L) X h (k + 1) = some (some (.inl s, n))) :
    ∃ s0 n0, Frame.stateAt (thread p L) X h k = some (some (.inl s0, n0)) ∧
      Startup.succ L h s0 e = some (some s) ∧ exit L h s = none := by
  rw [Frame.stateAt_succ he] at hσ
  cases hσ0 : Frame.stateAt (thread p L) X h k with
  | none => rw [hσ0] at hσ; simp at hσ
  | some o =>
    cases o with
    | none => rw [hσ0] at hσ; simp [Code.toMachine] at hσ
    | some σ =>
      rw [hσ0] at hσ
      obtain ⟨σ0, n0⟩ := σ
      change (thread p L h).next (σ0, n0) e = some (some (.inl s, n)) at hσ
      obtain ⟨h1, -⟩ := Code.counted_next_some (C := glued p L h) hσ
      rcases σ0 with s0 | ⟨i0, d0⟩
      swap
      · simp only [glued, Code.glue] at h1
        cases hr : (frag p L h i0).next d0 e with
        | none => rw [hr] at h1; simp at h1
        | some o' =>
          cases o' with
          | none => rw [hr] at h1; simp at h1
          | some d1 => rw [hr] at h1; simp at h1
      simp only [glued, Code.glue] at h1
      cases hs : Startup.succ L h s0 e with
      | none => simp [Startup.code, hs] at h1
      | some o' =>
        cases o' with
        | none => simp [Startup.code, hs] at h1
        | some s' =>
          simp only [Startup.code, hs, Option.map_some, Option.some.injEq] at h1
          unfold Code.enter at h1
          split at h1
          · simp at h1
          · rename_i hx
            simp only [Option.some.injEq, Sum.inl.injEq] at h1
            subst h1
            exact ⟨s0, n0, rfl, hs, hx⟩

/-- **A startup state has no barrier-0 event before it.** -/
theorem start_nobar0 (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {h : Nat} :
    ∀ k {s : Startup.D} {n : Cls → Nat},
      Frame.stateAt (thread p L) X h k = some (some (.inl s, n)) →
      ((X.tr h).take k).countP (Execution.isBarId 0) = 0 := by
  intro k
  induction k with
  | zero => intro s n _; simp
  | succ k ih =>
    intro s n hσ
    by_cases hk : k < (X.tr h).length
    swap
    · rw [Frame.stateAt_of_le (show (X.tr h).length ≤ k + 1 by omega),
        ← Frame.stateAt_of_le (show (X.tr h).length ≤ k by omega)] at hσ
      have := ih hσ
      rwa [List.take_of_length_le (show (X.tr h).length ≤ k + 1 by omega),
        ← List.take_of_length_le (show (X.tr h).length ≤ k by omega)]
    obtain ⟨e, he⟩ : ∃ e, (X.tr h)[k]? = some e := ⟨_, List.getElem?_eq_getElem hk⟩
    obtain ⟨s0, n0, hσ0, hs, hx⟩ := start_prev he hσ
    have hge : X.get (h, k) = some e := he
    rw [List.take_add_one, he, Option.toList_some, List.countP_append, ih hσ0]
    obtain ⟨pc, kind⟩ := e
    cases kind
    case bar id cnt mode =>
      obtain ⟨hE, hx0, -⟩ := start_fired hp hX hge hσ0
      rcases start_bar hE (rfl : Kind.bar id cnt mode = _) with hb | ⟨r, hr⟩
      · obtain ⟨site, x1, x2, x3⟩ := s0
        simp only at hb
        subst hb
        simp only [Startup.succ, Option.some.injEq] at hs
        subst hs
        exfalso
        unfold Startup.enterOf at hx
        split_ifs at hx <;> simp [exit] at hx
      · obtain ⟨site, x1, x2, x3⟩ := s0
        simp only at hr
        subst hr
        simp [exit] at hx0
    all_goals simp [Execution.isBarId]

theorem path_init_pos : ∀ k ≤ 54, ∀ q : Fin 34, pathSite.getD k .bar = .init q → k = initPos q := by
  decide

theorem initOff_inj : ∀ q q' : Fin 34, initOff q = initOff q' → q = q' := by decide

set_option maxHeartbeats 4000000 in
/-- **Every initialization event is the startup's**: an `mbarrier.init` event of a lane is fired
from a startup state at an initialization site `q` of a lane of warp 0, and initializes
`obj (initOff q)` of the lane's CTA with count `initCnt q`. -/
theorem init_event (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {h k pc c : Nat}
    {l : Loc} (hh : h < L.threads) (he : X.get (h, k) = some ⟨pc, .mbInit l c⟩) :
    Prologue.warpIndex L h = 0 ∧ ∃ q s n, Frame.stateAt (thread p L) X h k =
      some (some (.inl s, n)) ∧ s.site = .init q ∧ l = obj L h (initOff q) ∧ c = initCnt q := by
  have hT := table_shape_of hp hFw
  have hF := table_followed hp hX hFw
  obtain ⟨⟨σ1, n⟩, hσ, hJ, hi, hev⟩ := Frame.RoleTable.ev_of_ne_ubU (T := table p L)
    (S := fun g => g < L.threads) (fun g hg => thread_sound hp hg) hX hT hF hh he
    (fun f hf => by cases hf)
  have hJ' : JR p L h (σ1, n) := hJ
  rcases σ1 with s | ⟨i, d⟩
  swap
  · exfalso
    cases i with
    | epilogue => exact epi_noinit hev
    | correction =>
      rcases hev.1.data_or_vote with h | ⟨_,_,h⟩
      · exact corr_noinit h
      · cases h
    | softmax => exact soft_noinit hev.1
    | loader b => exact ld_noinit hev
    | mma =>
      rcases d with s | ⟨_, d⟩
      · rcases hev with ⟨_, _, _, hk⟩ | ⟨_, _, _, hk⟩ | ⟨_, _, hk⟩ | ⟨_, hk⟩ <;> cases hk
      · exact mma_noinit hev
    | stub r =>
      simp only [JR_eq] at hJ'
      split_ifs at hJ'
      · exact hJ'
      · unfold RefAll at hJ'
        split_ifs at hJ' <;> simp_all [Mma.Ref, Epilogue.Ref, LdWarp.Ref, CorrWarp.Ref]
  have hEv : Startup.Ev L h s ⟨pc, .mbInit l c⟩ := hev
  obtain ⟨site, x1, x2, x3⟩ := s
  have hsq : ∃ q, site = .init q := by
    cases site with
    | init q => exact ⟨q, rfl⟩
    | enter r => exact absurd rfl (jr_start_site hJ' r)
    | sh j =>
      fin_cases j <;> simp only [Startup.Ev] at hEv <;> obtain ⟨_, _, hk⟩ := hEv <;> cases hk
    | fence => simp only [Startup.Ev] at hEv; cases hEv
    | bar => simp only [Startup.Ev] at hEv; cases hEv
    | elect j =>
      simp only [Startup.Ev] at hEv
      rcases hEv with ⟨_, _, -, hk⟩ | ⟨_, hk⟩ <;> cases hk
  obtain ⟨q, rfl⟩ := hsq
  obtain ⟨hw0, hS0⟩ := jr_init hJ' (q := q) rfl
  have hx1 : x1 = BitVec.ofNat 64 L.sharedBase := (startAt0_of_mid (by rfl) hS0).2.1
  obtain ⟨t, ins, o', hat, -, hc, hfi⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ (by intro f h; cases h)
  rcases init_cnt hp (s := ⟨.init q, x1, x2, x3⟩) rfl hx1 hat hc hfi with hk | ⟨f, hk⟩
  · simp only [Kind.mbInit.injEq] at hk
    exact ⟨hw0, q, _, n, hσ, rfl, hk.1, hk.2⟩
  · cases hk

theorem pathSite_54 : pathSite.getD 54 .bar = .bar := by decide

set_option maxHeartbeats 4000000 in
/-- **The winner lane initializes an object at one position**: a lane of warp 0 that won an
election is at initialization site `q` only at position `initPos q`. -/
theorem init_pos (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {h k j0 : Nat}
    {e : Event} {s : Startup.D} {n : Cls → Nat} {q : Fin 34} (hh : InWarp L 0 h)
    (hσ : Frame.stateAt (thread p L) X h k = some (some (.inl s, n))) (hs : s.site = .init q)
    (he : X.get (h, k) = some e) (hub : ∀ f, e.kind ≠ .ub f) {pc0 inst0 : Nat}
    (hwon : X.get (h, j0) = some ⟨pc0, .elect (2 ^ 32 - 1) inst0 (laneOf L h)⟩) :
    k = initPos q := by
  have hsw : SameWarp L h h := ⟨⟨hh.1, hh.1, rfl⟩, rfl⟩
  have hlead : ∀ K, ∀ j < K, (∃ jj, pathSite.getD j .bar = .elect jj) →
      ∀ pc inst ld, X.get (h, j) = some ⟨pc, .elect (2 ^ 32 - 1) inst ld⟩ → ld = laneOf L h :=
    fun _ _ _ _ pc inst ld hx => elect_leader hX hx hwon hsw
  have hb := start_nobar0 hp hX k hσ
  by_cases hk : k ≤ 54
  · obtain ⟨s', n', hσ', hs', -⟩ := lead_path hp hX hh hk he hub hb (hlead k) k le_rfl
    rw [hσ] at hσ'
    simp only [Option.some.injEq, Prod.mk.injEq, Sum.inl.injEq] at hσ'
    rw [← hσ'.1, hs] at hs'
    exact path_init_pos k hk q hs'.symm
  · exfalso
    have hlen : k < (X.tr h).length := (List.getElem?_eq_some_iff.mp
      (show (X.tr h)[k]? = _ from he)).1
    obtain ⟨e54, he54⟩ : ∃ e, X.get (h, 54) = some e :=
      ⟨_, List.getElem?_eq_getElem (show 54 < (X.tr h).length by omega)⟩
    have hub54 : ∀ f, e54.kind ≠ .ub f := by
      intro f hf
      have := ub_last hX (show X.get (h, 54) = some ⟨e54.pc, .ub f⟩ by rw [he54, ← hf]) he
      omega
    have hb54 : ((X.tr h).take 54).countP (Execution.isBarId 0) = 0 := by
      have := countP_take_mono' (Execution.isBarId 0) (X.tr h) (show 54 ≤ k by omega)
      omega
    obtain ⟨s', n', hσ', hs', -⟩ := lead_path hp hX hh le_rfl he54 hub54 hb54 (hlead 54) 54 le_rfl
    rw [pathSite_54] at hs'
    have hE := (start_fired hp hX he54 hσ').1
    obtain ⟨site, x1, x2, x3⟩ := s'
    simp only at hs'
    subst hs'
    simp only [Startup.Ev] at hE
    have h55 : ((X.tr h).take 55).countP (Execution.isBarId 0) = 1 := by
      rw [List.take_add_one, show (X.tr h)[54]? = some e54 from he54, Option.toList_some,
        List.countP_append, hb54]
      obtain ⟨pc, kind⟩ := e54
      simp only at hE
      subst hE
      simp [Execution.isBarId]
    have := countP_take_mono' (Execution.isBarId 0) (X.tr h) (show 55 ≤ k by omega)
    omega

set_option maxHeartbeats 4000000 in
/-- **Each object is initialized by one event, with one count.** -/
theorem init_unique (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {i i' : EvId}
    {pc pc' c c' : Nat} {l : Loc} (hh : i.1 < L.threads) (hh' : i'.1 < L.threads)
    (he : X.get i = some ⟨pc, .mbInit l c⟩) (he' : X.get i' = some ⟨pc', .mbInit l c'⟩) :
    i = i' ∧ c = c' := by
  obtain ⟨h, k⟩ := i
  obtain ⟨h', k'⟩ := i'
  obtain ⟨hw, q, s, n, hσ, hs, hl, hc⟩ := init_event hp hX hFw hh he
  obtain ⟨hw', q', s', n', hσ', hs', hl', hc'⟩ := init_event hp hX hFw hh' he'
  rw [hl] at hl'
  simp only [obj, Loc.mk.injEq, true_and, Nat.add_left_cancel_iff] at hl'
  obtain ⟨hcta, hq⟩ := hl'
  have hqq := initOff_inj q q' hq
  subst hqq
  obtain ⟨j, -, pcj, instj, hj⟩ := init_won hp hX k hσ ⟨q, hs⟩
  obtain ⟨j', -, pcj', instj', hj'⟩ := init_won hp hX k' hσ' ⟨q, hs'⟩
  have hsw : SameWarp L h h' := ⟨⟨hh, hh', hcta⟩, by
    have h1 : h % L.block / 32 = 0 := hw
    have h2 : h' % L.block / 32 = 0 := hw'
    omega⟩
  have hlane := elect_winner hX hj hj' hsw
  have hhh : h = h' := by
    have h1 : h % L.block / 32 = 0 := hw
    have h2 : h' % L.block / 32 = 0 := hw'
    simp only [laneOf] at hlane
    have e1 := Nat.div_add_mod h L.block
    have e2 := Nat.div_add_mod h' L.block
    rw [hcta] at e1
    omega
  subst hhh
  have hub : ∀ f, (⟨pc, .mbInit l c⟩ : Event).kind ≠ .ub f := fun f hf => by cases hf
  have hub' : ∀ f, (⟨pc', .mbInit l c'⟩ : Event).kind ≠ .ub f := fun f hf => by cases hf
  have hk := init_pos hp hX ⟨hh, hw⟩ hσ hs he hub hj
  have hk' := init_pos hp hX ⟨hh, hw⟩ hσ' hs' he' hub' hj
  exact ⟨by rw [hk, hk'], by rw [hc, hc']⟩

/-! ### Initialized first -/

/-- **A record's issuer names its object**, and an issuer that is an initialization of it issued
an initialization record. -/
theorem rec_issuer (hX : Consistent L kernel Assumptions.all m X) {o : Loc}
    {r : MBarrier.Record AsyncCopy.Ref} (hr : r ∈ X.objects o) :
    ∃ ev, X.get r.id.issuer = some ev ∧ Frame.MbarOf ev o ∧
      ((∃ c, ev.kind = .mbInit o c) → ∃ n, r.action = .init n) := by
  cases AsyncCopy.record_source hX.tma.2.2.1 hr with
  | init hid he ha => rw [hid]; exact ⟨_, he, rfl, fun _ => ⟨_, ha⟩⟩
  | inval hid he ha =>
    rw [hid]; exact ⟨_, he, rfl, fun ⟨_, h⟩ => by cases h⟩
  | arrive hid he ha =>
    rw [hid]; exact ⟨_, he, rfl, fun ⟨_, h⟩ => by cases h⟩
  | wait hid he ha =>
    rw [hid]; exact ⟨_, he, rfl, fun ⟨_, h⟩ => by cases h⟩
  | increment hid he ha =>
    rw [hid]; exact ⟨_, he, rfl, fun ⟨_, h⟩ => by cases h⟩
  | tensor hid he hm ha =>
    rw [hid]; exact ⟨_, he, hm, fun ⟨_, h⟩ => by cases h⟩
  | arriveOn hid he hm hn ha =>
    rw [hid]; exact ⟨_, he, hm.symm, fun ⟨_, h⟩ => by cases h⟩
  | bulk hid he hc hn ha =>
    rw [hid]; exact ⟨_, he, hc, fun ⟨_, h⟩ => by cases h⟩
  | commit hid he ht ha =>
    rw [hid]; exact ⟨_, he, ⟨_, ht⟩, fun ⟨_, h⟩ => by cases h⟩
  | clc hid he hm htg ha =>
    rw [hid]; exact ⟨_, he, ⟨_, htg, hm⟩, fun ⟨_, h⟩ => by cases h⟩

theorem initCnt_valid : ∀ q, MBarrier.validCount (initCnt q) := by decide

set_option maxHeartbeats 4000000 in
/-- **An initialization of an object, published to every other use of it.** Every event that
names `obj L g (initOff q)` and is no initialization of it has the object's initialization, with
count `initCnt q`, published to it. -/
theorem pub_of_use (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) {g : Nat} {q : Fin 34}
    {i : EvId} {ev : Event} (he : X.get i = some ev) (hm : Frame.MbarOf ev (obj L g (initOff q)))
    (hni : ∀ c, ev.kind ≠ .mbInit (obj L g (initOff q)) c) :
    ∃ j, X.MbInit j (obj L g (initOff q)) (initCnt q) ∧
      InitPublished L X j i (obj L g (initOff q)) := by
  have hT := table_shape_of hp hFw
  have hF := table_followed hp hX hFw
  obtain ⟨h, k⟩ := i
  have hh := Frame.lt_of_get hX he
  have hub : ∀ f, ev.kind ≠ .ub f := by
    obtain ⟨pc, kd⟩ := ev
    rintro f rfl
    simp only [Frame.MbarOf] at hm
  obtain ⟨σ, hσ, hJ, hi, hev⟩ := Frame.RoleTable.ev_of_ne_ubU (T := table p L)
    (S := fun g => g < L.threads) (fun g hg => thread_sound hp hg) hX hT hF hh he hub
  obtain ⟨j, c, ⟨pcj, hj⟩, hpub, -⟩ := use_pub hp hX hFw hh he hσ hJ hi hev hm hni
  obtain ⟨-, q', s, n, -, -, hl, hc⟩ := init_event hp hX hFw
    (Frame.lt_of_get hX hj) hj
  simp only [obj, Loc.mk.injEq, true_and, Nat.add_left_cancel_iff] at hl
  rw [initOff_inj q' q hl.2.symm] at hc
  subst hc
  exact ⟨j, ⟨pcj, hj⟩, hpub⟩

set_option maxHeartbeats 4000000 in
/-- **Every object is initialized first**: its history starts with its one initialization,
without fault, with count `initCnt q`. -/
theorem obj_initFirst (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (g : Nat) (q : Fin 34) :
    PairTmaRing.InitFirst X (obj L g (initOff q)) (initCnt q) := by
  intro r hr
  obtain ⟨ev, hget, hm, -⟩ := rec_issuer hX hr
  -- the object's initialization
  obtain ⟨e, he⟩ : ∃ e, X.MbInit e (obj L g (initOff q)) (initCnt q) := by
    by_cases hi : ∃ c, ev.kind = .mbInit (obj L g (initOff q)) c
    · obtain ⟨c, hc⟩ := hi
      obtain ⟨pc, kd⟩ := ev
      simp only at hc
      subst hc
      obtain ⟨-, q', s, n, -, -, hl, hcq⟩ := init_event hp hX hFw
        (Frame.lt_of_get hX hget) hget
      simp only [obj, Loc.mk.injEq, true_and, Nat.add_left_cancel_iff] at hl
      rw [initOff_inj q' q hl.2.symm] at hcq
      subst hcq
      exact ⟨_, pc, hget⟩
    · push Not at hi
      obtain ⟨j, hj, -⟩ := pub_of_use hp hX hFw hget hm hi
      exact ⟨j, hj⟩
  refine initFirst_of_published hX he (initCnt_valid q) (fun i pc n hi => ?_) (fun s hs hn => ?_)
    r hr
  · obtain ⟨pce, hge⟩ := he
    exact init_unique hp hX hFw (Frame.lt_of_get hX hi) (Frame.lt_of_get hX hge) hi
      hge
  · obtain ⟨ev', hget', hm', hnot⟩ := rec_issuer hX hs
    have hni : ∀ c, ev'.kind ≠ .mbInit (obj L g (initOff q)) c := by
      intro c hc
      obtain ⟨n, hn'⟩ := hnot ⟨c, hc⟩
      exact hn n hn'
    obtain ⟨j, ⟨pcj, hj⟩, hpub⟩ := pub_of_use hp hX hFw hget' hm' hni
    obtain ⟨pce, hge⟩ := he
    have := (init_unique hp hX hFw (Frame.lt_of_get hX hj) (Frame.lt_of_get hX hge)
      hj hge).1
    rwa [this] at hpub

end
end PTX.Kernels.TmlFa4Fwd.Proof
