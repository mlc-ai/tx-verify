-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStatic
public import Kernels.FlashAttn4Fwd.Proof.Thread.Origin
public import Kernels.FlashAttn4Fwd.Proof.Interface.Older
public import Kernels.FlashAttn4Fwd.Proof.Interface.Exit
public import Kernels.FlashAttn4Fwd.Proof.Interface.Output
public import Lemmas.Flow.WaitAcquire

@[expose] public section

/-! # The correction warps' statistics barriers and credits

An event of a thread of warps 8 to 11 is fired from a prologue state (of a prologue kind) or
from a correction state, with the role's run invariant (`Correction.Counts`), its state
invariant and its site's event (`corr_origin`). From the site events: the thread's
named-barrier events are the start and end barriers (`bar 2, 416`) and the syncs of its two
statistics barriers (`k + 3`, `k + 7` with `k = w - 8`, count 64), so its count of events on a
statistics barrier is its count of syncs there (`barOrd_corr`). The credit arrivals and the
loads of the statistics words follow one more sync of the stage than credits of the stage
(`Counts.sync`, `Counts.credit` at the sites `credit a`, `ldA st`, `ldL st`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A correction warp's index in the group is its warp less 8. -/
theorem corr_kOf {g : Nat} (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12) :
    Correction.kOf L g = warpOf L g - 8 := by
  simp only [Correction.kOf, Correction.tidOf, warpOf] at *
  omega

/-- **The origin of a correction thread's event**: a prologue event, or the site event of a
correction state with the role's run invariant. -/
theorem corr_origin (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12) (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) :
    (∃ p, Frame.stateAt (code L) X g k = some (some (.inl p)) ∧ Prologue.ProKind e.kind) ∨
    ∃ (d : Correction.D) (t : TState) (ins : Instr) (o : Option TState),
      Frame.stateAt (code L) X g k = some (some (.inr (.corr d))) ∧
      Correction.Counts L g d ((X.tr g).take k) ∧ Correction.Inv L g d ∧
      (t.pc = d.site.pc ∧ t.sub = d.site.sub ∧ t.acc = [] ∧ t.fault = none ∧
        Holds t.regs (Correction.facts L g d)) ∧
      kernel.code[d.site.pc]? = some ins ∧ Fires d.site.pc (eventTmpl asms L g t ins.op) e o ∧
      (e.kind ≠ .exit → Correction.Ev L g d e) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ :=
    event_origin hpre hX ht (fun g hg => roleJ_run hpre hg) he hub
  rcases d with p | r
  · refine .inl ⟨p, hσ, ?_⟩
    exact (pro_event hpre hX he hσ (fun f h => hub e.pc f (by rw [← h]))).proKind
  · have hrw := role_warp_run hpre hg (Frame.trace (C := code L) (fun _ hg => sound hpre hg) hX hg)
      k r hσ
    cases r with
    | corr d =>
      refine .inr ⟨d, t, ins, o, hσ, hJ, hi, hat, hc, hf, fun hx => ?_⟩
      cases o with
      | some u =>
        exact Correction.site_event hpre hg hi hat hc hf
      | none =>
        exfalso
        cases hm : eventTmpl asms L g t ins.op <;> rw [hm] at hf <;> simp [Fires] at hf
        · exact hx (by rw [hf])
        · exact hub _ _ hf
    | _ => simp only [Role.kind, RoleKind.Warp] at hrw; omega

/-- The role's trips are at least one. -/
theorem corr_trips_pos (hpre : Pre P L mem0) : 1 ≤ Correction.trips L := by
  have := skOf_eq hpre; have := hpre.skPos
  unfold Correction.trips; omega

/-- The stage of a credit arrival is the stage of its barrier. -/
theorem corr_credit_site {g : Nat} {a : Fin 6} {st : Nat}
    (h : Correction.ownLoc L g (240 + 8 * (a.val % 2)) = statsBar L (ctaOf L g) st) :
    a.val % 2 = st := by
  simp only [Correction.ownLoc, statsBar, Correction.sb, Loc.mk.injEq] at h
  omega

/-- The correction's remote arrivals and its O-full polls are sites of the cluster-scope
assumption. -/
theorem corr_clusterSites :
    (Correction.Site.free 0).pc ∈ Assumptions.clusterMbarSites ∧
    (Correction.Site.free 1).pc ∈ Assumptions.clusterMbarSites ∧
    (∀ st : Fin 2, ∀ b : Bool, (Correction.Site.oFree st b).pc ∈ Assumptions.clusterMbarSites) ∧
    (∀ st : Fin 2, (Correction.Site.oWait st).pc ∈ Assumptions.clusterMbarSites) := by
  refine ⟨by decide, by decide, fun st b => ?_, fun st => ?_⟩
  · fin_cases st <;> cases b <;> decide
  · fin_cases st <;> decide


/-- The instruction at `pc` is a `ret`. -/
def retAt (pc : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨_, .ret⟩ | some ⟨_, .exit⟩ => true
  | _ => false

set_option maxHeartbeats 4000000 in
/-- Only the exit site of the correction is a `ret`. -/
theorem corr_ret_site (s : Correction.Site) (hs : s ≠ .exit) : retAt s.pc = false := by
  rcases s with _ | _ | st | ⟨st, gen⟩ | a | st | st | ⟨st, j⟩ | ⟨st, j⟩ | ⟨st, j⟩ |
    st | ⟨st, fin⟩ | st | st | st | ⟨st, j⟩ | ⟨st, j⟩ | ⟨st, j, h, el⟩ | st | st | _ | _ | _
  all_goals (try fin_cases st)
  all_goals (try fin_cases a)
  all_goals (try cases gen)
  all_goals (try cases fin)
  all_goals (try fin_cases j)
  all_goals (try fin_cases h)
  all_goals first | exact absurd rfl hs | (simp only [Correction.Site.pc]; decide +kernel)

/-- The role's trips are the key blocks. -/
theorem corr_trips_eq (hpre : Pre P L mem0) : Correction.trips L = kvBlocks P := by
  rw [Correction.trips, kvBlocks, skOf_eq hpre]

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- **A correction thread's named-barrier event**: the start or end barrier (`bar 2, 416`), or a
sync of one of its statistics barriers. -/
theorem corr_bar {g i pc id : Nat} {cnt : Option Nat} {m : BarMode}
    (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12)
    (he : X.get (g, i) = some ⟨pc, .bar id cnt m⟩) :
    (id = 2 ∧ cnt = some 416) ∨
      (cnt = some 64 ∧ m = .sync ∧ ∃ st < 2, id = warpOf L g - 5 + 4 * st) := by
  rcases corr_origin hpre hX ht he hw hw' (fun _ _ h => by cases h) with ⟨p, -, hk⟩ |
    ⟨d, t, ins, o, -, -, -, -, -, -, hev⟩
  · cases hk
  obtain ⟨-, hk⟩ := hev (by simp)
  have hkw := corr_kOf hw hw'
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  cases site <;> simp at hk
  · exact .inl ⟨hk.1, hk.2.1⟩
  · rename_i st _
    refine .inr ⟨hk.2.1, hk.2.2, st.val, st.isLt, ?_⟩
    rw [hk.1, hkw]; omega
  · exact .inl ⟨hk.1, hk.2.1⟩

/-- **The statistics-barrier ordinal of a correction thread** is its count of syncs there. -/
theorem corr_barOrd {g : Nat} (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12) (i : Nat)
    {id : Nat} (hid : id ≠ 2) :
    barOrd X g i id = barEvents id 64 .sync ((X.tr g).take i) := by
  unfold barOrd barEvents
  apply List.countP_congr
  intro x hx
  obtain ⟨j, -, hj⟩ := get_of_mem_take hx
  obtain ⟨pc, k⟩ := x
  constructor
  · intro h
    cases k <;> simp only [Execution.isBarId, beq_iff_eq, reduceCtorEq] at h
    rename_i id' cnt m
    subst h
    rcases corr_bar hpre hX ht hw hw' hj with ⟨rfl, -⟩ | ⟨rfl, rfl, -⟩
    · exact absurd rfl hid
    · simp [barIs]
  · intro h
    cases k <;> simp only [barIs] at h
    all_goals (try split at h) <;> simp_all [Execution.isBarId]


/-- **A correction thread's arrival**: one arrival without bytes, at a credit site on its stage's
statistics barrier, at a staged site on the stage's staged barrier, or at an O-free site on the
leader's P-ready barrier of the stage. -/
theorem corr_arrive {g i pc tx cnt : Nat} {m : Loc} {rel : Bool} {sc : MbarScope}
    (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12)
    (he : X.get (g, i) = some ⟨pc, .arrive m tx cnt rel sc⟩) :
    tx = 0 ∧ cnt = 1 ∧ ∃ d : Correction.D,
      Frame.stateAt (code L) X g i = some (some (.inr (.corr d))) ∧
      Correction.Counts L g d ((X.tr g).take i) ∧ Correction.Inv L g d ∧ d.site.pc = pc ∧
      ((∃ a : Fin 6, d.site = .credit a ∧ m = Correction.ownLoc L g (240 + 8 * (a.val % 2))) ∨
        (∃ st : Fin 2, d.site = .staged st ∧ m = Correction.ownLoc L g (256 + 8 * st.val)) ∨
        (∃ st : Fin 2, (d.site = .free st ∨ ∃ b, d.site = .oFree st b) ∧
          m = Correction.leadLoc L g (144 + 8 * st.val))) := by
  rcases corr_origin hpre hX ht he hw hw' (fun _ _ h => by cases h) with ⟨p, -, hk⟩ |
    ⟨d, t, ins, o, hσ, hJ, hi, -, -, -, hev⟩
  · cases hk
  obtain ⟨hpc, hk⟩ := hev (by simp)
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  have hin {l : Loc} {tx' cnt' : Nat} (h : ∃ rel' sc', Kind.arrive m tx cnt rel sc =
      Kind.arrive l tx' cnt' rel' sc') : m = l ∧ tx = tx' ∧ cnt = cnt' := by
    obtain ⟨_, _, h⟩ := h
    injection h with h1 h2 h3
    exact ⟨h1, h2, h3⟩
  cases site
  case free st =>
    obtain ⟨h1, h2, h3⟩ := hin hk
    exact ⟨h2, h3, _, hσ, hJ, hi, hpc.symm, .inr (.inr ⟨st, .inl rfl, h1⟩)⟩
  case credit a0 =>
    obtain ⟨h1, h2, h3⟩ := hin hk
    exact ⟨h2, h3, _, hσ, hJ, hi, hpc.symm, .inl ⟨a0, rfl, h1⟩⟩
  case oFree st b =>
    obtain ⟨h1, h2, h3⟩ := hin hk
    exact ⟨h2, h3, _, hσ, hJ, hi, hpc.symm, .inr (.inr ⟨st, .inr ⟨b, rfl⟩, h1⟩)⟩
  case staged st =>
    obtain ⟨h1, h2, h3⟩ := hin hk
    exact ⟨h2, h3, _, hσ, hJ, hi, hpc.symm, .inr (.inl ⟨st, rfl, h1⟩)⟩
  all_goals exfalso
  all_goals simp at hk

/-- **`StatsFacts.corr_credit`**: a correction thread's credit arrival of stage `st` follows one
more sync of its statistics barrier of the stage than its earlier credit arrivals. -/
theorem StatsFacts_corr_credit {g i pc st tx cnt : Nat} {m : Loc} {rel : Bool} {sc : MbarScope}
    (_hg : g < L.threads) (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12) (hst : st < 2)
    (he : X.get (g, i) = some ⟨pc, .arrive m tx cnt rel sc⟩) (hm : m = statsBar L (ctaOf L g) st) :
    arrivals m ((X.tr g).take i) + 1 = barOrd X g i (warpOf L g - 5 + 4 * st) := by
  obtain ⟨-, -, d, -, hc, hi, -, hs⟩ := corr_arrive hpre hX ht hw hw' he
  have hkw := corr_kOf hw hw'
  have hT := corr_trips_pos hpre
  rw [corr_barOrd hpre hX ht hw hw' i (by omega)]
  subst hm
  rcases hs with ⟨a, hsa, hma⟩ | ⟨st', -, hma⟩ | ⟨st', -, hma⟩
  · have hst' := corr_credit_site hma.symm
    subst hst'
    have h1 := hc.credit (a.val % 2) (by omega)
    have h2 := hc.sync (a.val % 2) (by omega)
    have hid : warpOf L g - 5 + 4 * (a.val % 2) = Correction.kOf L g + 3 + 4 * (a.val % 2) := by
      omega
    rw [hid, h2, hma, h1]
    have htr := hi.trip
    obtain ⟨site, i', tt, aw, aa, o⟩ := d
    simp only at hsa htr ⊢
    subst hsa
    fin_cases a <;>
      simp [Correction.creditPos, Correction.syncPos, Correction.Site.inTrip] at htr ⊢ <;> omega
  · simp only [Correction.ownLoc, statsBar, Correction.sb, Loc.mk.injEq] at hma
    omega
  · simp only [Correction.leadLoc, statsBar, Correction.sb, Loc.mk.injEq] at hma
    omega


/-- **A correction thread's poll**: of its stage's O-full barrier with the parity of its item, of
its stage's staging-free barrier or (at the tail) of stage 1's, with the parity of the next
item. -/
theorem corr_wait {g i pc p : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope}
    (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12)
    (he : X.get (g, i) = some ⟨pc, .wait m p ok acq sc⟩) :
    ∃ d : Correction.D,
      Frame.stateAt (code L) X g i = some (some (.inr (.corr d))) ∧
      Correction.Counts L g d ((X.tr g).take i) ∧ Correction.Inv L g d ∧ d.site.pc = pc ∧
      ((∃ st : Fin 2, d.site = .oWait st ∧ m = Correction.ownLoc L g (192 + 8 * st.val) ∧
          p = d.i % 2) ∨
        (∃ st : Fin 2, d.site = .fWait st ∧ m = Correction.ownLoc L g (272 + 8 * st.val) ∧
          p = (d.i + 1) % 2) ∨
        (d.site = .tailWait ∧ m = Correction.ownLoc L g 280 ∧ p = (d.i + 1) % 2)) := by
  rcases corr_origin hpre hX ht he hw hw' (fun _ _ h => by cases h) with ⟨p, -, hk⟩ |
    ⟨d, t, ins, o, hσ, hJ, hi, -, -, -, hev⟩
  · cases hk
  obtain ⟨hpc, hk⟩ := hev (by simp)
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  have hin {l : Loc} {p' : Nat} (h : ∃ ok' acq' sc', Kind.wait m p ok acq sc =
      Kind.wait l p' ok' acq' sc') : m = l ∧ p = p' := by
    obtain ⟨_, _, _, h⟩ := h
    injection h with h1 h2
    exact ⟨h1, h2⟩
  cases site
  case oWait st =>
    obtain ⟨h1, h2⟩ := hin hk
    exact ⟨_, hσ, hJ, hi, hpc.symm, .inl ⟨st, rfl, h1, h2⟩⟩
  case fWait st =>
    obtain ⟨h1, h2⟩ := hin hk
    exact ⟨_, hσ, hJ, hi, hpc.symm, .inr (.inl ⟨st, rfl, h1, h2⟩)⟩
  case tailWait =>
    obtain ⟨h1, h2⟩ := hin hk
    exact ⟨_, hσ, hJ, hi, hpc.symm, .inr (.inr ⟨rfl, h1, h2⟩)⟩
  all_goals exfalso
  all_goals simp at hk

/-- **`StatsFacts.bar_form`, correction part.** -/
theorem Facts.Corr.bar_form {g i pc id : Nat} {cnt : Option Nat} {m : BarMode}
    (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12)
    (he : X.get (g, i) = some ⟨pc, .bar id cnt m⟩) : (id = 2 ∧ cnt = some 416) ∨
      (cnt = some 64 ∧ ((warpOf L g < 8 ∧ id = warpOf L g + 3 ∧ m = .arrive) ∨
        (8 ≤ warpOf L g ∧ warpOf L g < 12 ∧ (id = warpOf L g - 5 ∨ id = warpOf L g - 1) ∧
          m = .sync))) := by
  rcases corr_bar hpre hX ht hw hw' he with h | ⟨h1, h2, st, hst, rfl⟩
  · exact .inl h
  · refine .inr ⟨h1, .inr ⟨hw, hw', ?_, h2⟩⟩
    rcases (show st = 0 ∨ st = 1 by omega) with rfl | rfl
    · exact .inl (by omega)
    · exact .inr (by omega)

/-- **`StatsFacts.credit_arrive`, correction part.** -/
theorem Facts.Corr.credit_arrive {g i pc tx cnt c st : Nat} {rel : Bool} {sc : MbarScope}
    (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12) (hst : st < 2)
    (he : X.get (g, i) = some ⟨pc, .arrive (statsBar L c st) tx cnt rel sc⟩) :
    8 ≤ warpOf L g ∧ warpOf L g < 12 ∧ c = ctaOf L g ∧ tx = 0 ∧ cnt = 1 ∧ rel = true := by
  obtain ⟨htx, hcnt, d, -, -, -, -, hs⟩ := corr_arrive hpre hX ht hw hw' he
  refine ⟨hw, hw', ?_, htx, hcnt, (Static.arrive_attr hX he).1⟩
  rcases hs with ⟨a, -, hm⟩ | ⟨st', -, hm⟩ | ⟨st', -, hm⟩ <;>
    simp only [Correction.ownLoc, Correction.leadLoc, statsBar, Correction.sb,
      Loc.mk.injEq] at hm <;> omega

/-- **`OutputFacts.staged_arrive`, correction part.** -/
theorem Facts.Corr.staged_arrive {g i pc tx cnt c st : Nat} {rel : Bool} {sc : MbarScope}
    (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12) (hst : st < 2)
    (he : X.get (g, i) = some ⟨pc, .arrive (stagedBar L c st) tx cnt rel sc⟩) :
    8 ≤ warpOf L g ∧ warpOf L g < 12 ∧ c = ctaOf L g ∧ tx = 0 ∧ cnt = 1 ∧ rel = true ∧
      arrivals (stagedBar L c st) ((X.tr g).take i) + 1 ≤
        okPolls (freeBar L c st) ((X.tr g).take i) := by
  obtain ⟨htx, hcnt, d, -, hc, -, -, hs⟩ := corr_arrive hpre hX ht hw hw' he
  have hrel := (Static.arrive_attr hX he).1
  rcases hs with ⟨a, -, hm⟩ | ⟨st', hsd, hm⟩ | ⟨st', -, hm⟩
  · simp only [Correction.ownLoc, stagedBar, Correction.sb, Loc.mk.injEq] at hm; omega
  · simp only [Correction.ownLoc, stagedBar, Correction.sb, Loc.mk.injEq] at hm
    obtain ⟨-, rfl, hst'⟩ := hm
    have hst'' : st = st'.val := by omega
    subst hst''
    refine ⟨hw, hw', rfl, htx, hcnt, hrel, ?_⟩
    have h1 := hc.staged st'.val st'.isLt
    have h2 := hc.oFree st'.val st'.isLt
    simp only [Correction.ownLoc, Correction.sb] at h1 h2
    simp only [stagedBar, freeBar]
    rw [h1, h2]
    obtain ⟨site, i', tt, aw, aa, o⟩ := d
    simp only at hsd ⊢
    subst hsd
    fin_cases st' <;> simp [Correction.stagedPos, Correction.fPos]
  · simp only [Correction.leadLoc, stagedBar, Correction.sb, Loc.mk.injEq] at hm; omega

/-- **`PReadyFacts.p_arrive`, correction part.** -/
theorem Facts.Corr.p_arrive {g i pc tx cnt c st : Nat} {rel : Bool} {sc : MbarScope}
    (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12) (hst : st < 2)
    (he : X.get (g, i) = some ⟨pc, .arrive (pReadyBar L c st) tx cnt rel sc⟩) :
    leadCta (ctaOf L g) = c ∧
      ((warpOf L g < 8 ∧ warpOf L g / 4 = st) ∨ (8 ≤ warpOf L g ∧ warpOf L g < 12)) ∧
      tx = 0 ∧ cnt = 1 ∧ rel = true ∧ sc = .cluster := by
  obtain ⟨htx, hcnt, d, -, -, -, hpc, hs⟩ := corr_arrive hpre hX ht hw hw' he
  have hat := Static.arrive_attr hX he
  obtain ⟨hc0, hc1, hcf, -⟩ := corr_clusterSites
  rcases hs with ⟨a, -, hm⟩ | ⟨st', -, hm⟩ | ⟨st', hsd, hm⟩
  · simp only [Correction.ownLoc, pReadyBar, Correction.sb, Loc.mk.injEq] at hm; omega
  · simp only [Correction.ownLoc, pReadyBar, Correction.sb, Loc.mk.injEq] at hm; omega
  · simp only [Correction.leadLoc, pReadyBar, Correction.sb, Loc.mk.injEq] at hm
    refine ⟨by simp only [leadCta]; omega, .inr ⟨hw, hw'⟩, htx, hcnt, hat.1, hat.2 ?_⟩
    rw [← hpc]
    rcases hsd with h | ⟨b, h⟩ <;> rw [h]
    · fin_cases st'
      · exact hc0
      · exact hc1
    · exact hcf st' b

/-- **`OFullFacts.o_poll`, correction part.** -/
theorem Facts.Corr.o_poll {g i pc p c st : Nat} {ok acq : Bool} {sc : MbarScope}
    (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12) (hst : st < 2)
    (he : X.get (g, i) = some ⟨pc, .wait (oFullBar L c st) p ok acq sc⟩) :
    ctaOf L g = c ∧ 8 ≤ warpOf L g ∧ warpOf L g < 12 ∧
      p % 2 = okPolls (oFullBar L c st) ((X.tr g).take i) % 2 ∧
      (ok = true → acq = true ∧ sc = .cluster) := by
  obtain ⟨d, -, hc, -, hpc, hs⟩ := corr_wait hpre hX ht hw hw' he
  have hat := Static.wait_attr hX he
  rcases hs with ⟨st', hsd, hm, hp⟩ | ⟨st', -, hm, -⟩ | ⟨-, hm, -⟩
  · simp only [Correction.ownLoc, oFullBar, Correction.sb, Loc.mk.injEq] at hm
    obtain ⟨-, rfl, hst'⟩ := hm
    have hst'' : st = st'.val := by omega
    subst hst''
    refine ⟨rfl, hw, hw', ?_, fun _ => ⟨hat.1, hat.2 ?_⟩⟩
    · have h1 := hc.oFull st'.val st'.isLt
      rw [show oFullBar L (ctaOf L g) st'.val = Correction.ownLoc L g (192 + 8 * st'.val) by
        simp only [oFullBar, Correction.ownLoc, Correction.sb], h1, hp]
      obtain ⟨site, i', tt, aw, aa, o⟩ := d
      simp only at hsd ⊢
      subst hsd
      fin_cases st' <;> simp [Correction.oPos]
    · rw [← hpc, hsd]; exact corr_clusterSites.2.2.2 st'
  · simp only [Correction.ownLoc, oFullBar, Correction.sb, Loc.mk.injEq] at hm; omega
  · simp only [Correction.ownLoc, oFullBar, Correction.sb, Loc.mk.injEq] at hm; omega

/-- **`OutputFacts.free_poll`, correction part.** -/
theorem Facts.Corr.free_poll {g i pc p c st : Nat} {ok acq : Bool} {sc : MbarScope}
    (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12) (hst : st < 2)
    (he : X.get (g, i) = some ⟨pc, .wait (freeBar L c st) p ok acq sc⟩) :
    8 ≤ warpOf L g ∧ warpOf L g < 12 ∧ c = ctaOf L g ∧
      p % 2 = (okPolls (freeBar L c st) ((X.tr g).take i) + 1) % 2 ∧ (ok = true → acq = true) := by
  obtain ⟨d, -, hc, -, -, hs⟩ := corr_wait hpre hX ht hw hw' he
  have hat := Static.wait_attr hX he
  have hfree : ∀ s : Nat, s < 2 → freeBar L (ctaOf L g) s = Correction.ownLoc L g (272 + 8 * s) :=
    fun s _ => by simp only [freeBar, Correction.ownLoc, Correction.sb]
  rcases hs with ⟨st', -, hm, -⟩ | ⟨st', hsd, hm, hp⟩ | ⟨hsd, hm, hp⟩
  · simp only [Correction.ownLoc, freeBar, Correction.sb, Loc.mk.injEq] at hm; omega
  · simp only [Correction.ownLoc, freeBar, Correction.sb, Loc.mk.injEq] at hm
    obtain ⟨-, rfl, hst'⟩ := hm
    have hst'' : st = st'.val := by omega
    subst hst''
    refine ⟨hw, hw', rfl, ?_, fun _ => hat.1⟩
    rw [hfree _ st'.isLt, hc.oFree st'.val st'.isLt, hp]
    obtain ⟨site, i', tt, aw, aa, o⟩ := d
    simp only at hsd ⊢
    subst hsd
    fin_cases st' <;> simp [Correction.fPos]
  · simp only [Correction.ownLoc, freeBar, Correction.sb, Loc.mk.injEq] at hm
    obtain ⟨-, rfl, hst'⟩ := hm
    obtain rfl : st = 1 := by omega
    refine ⟨hw, hw', rfl, ?_, fun _ => hat.1⟩
    rw [hfree 1 (by decide), hc.oFree 1 (by decide), hp]
    obtain ⟨site, i', tt, aw, aa, o⟩ := d
    simp only at hsd ⊢
    subst hsd
    simp [Correction.fPos]


/-- **A correction thread's exit** is at the exit site. -/
theorem corr_exit_state {g k pc : Nat} (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12)
    (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    ∃ d : Correction.D, Frame.stateAt (code L) X g k = some (some (.inr (.corr d))) ∧
      Correction.Counts L g d ((X.tr g).take k) ∧ Correction.Inv L g d ∧ d.site = .exit := by
  rcases corr_origin hpre hX ht he hw hw' (fun _ _ h => by cases h) with ⟨p, -, hk⟩ |
    ⟨d, t, ins, o, hσ, hJ, hi, -, hc, hf, -⟩
  · cases hk
  refine ⟨d, hσ, hJ, hi, ?_⟩
  by_contra hs
  have hr := corr_ret_site d.site hs
  obtain ⟨gd, op⟩ := ins
  rcases fires_exit_op hf rfl with hop | hop <;>
    (simp only at hop; subst hop; simp [retAt, hc] at hr)

/-- **`ExitFacts.corr_exit`**: at its exit a correction thread has polled each stage's O-full
barrier once per item of its cluster. -/
theorem ExitFacts_corr_exit {g k pc u st : Nat} (_hg : g < L.threads) (hw : 8 ≤ warpOf L g)
    (hw' : warpOf L g < 12) (he : X.get (g, k) = some ⟨pc, .exit⟩) (hst : st < 2)
    (hu : workOf L g u < totOf L) :
    u < okPolls (oFullBar L (ctaOf L g) st) ((X.tr g).take k) := by
  obtain ⟨d, -, hc, hi, hs⟩ := corr_exit_state hpre hX ht hw hw' he
  have h1 := hc.oFull st hst
  rw [show oFullBar L (ctaOf L g) st = Correction.ownLoc L g (192 + 8 * st) by
    simp only [oFullBar, Correction.ownLoc, Correction.sb], h1]
  have hti := hi.tail (by rw [hs]; rfl) (by rw [hs]; simp) (by rw [hs]; simp)
    (fun _ => by rw [hs]; simp)
  have hu' := (Correction.lt_items_iff (g := g) hpre).mpr hu
  rw [hti]
  omega

/-- A correction thread with no start-barrier event before event `b` has no event on barrier 2
there. -/
theorem corr_barOrd2_zero {g b : Nat} (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12)
    (h0 : barEvents 2 416 .sync ((X.tr g).take b) = 0)
    (h1 : barEvents 2 416 .arrive ((X.tr g).take b) = 0) : barOrd X g b 2 = 0 := by
  unfold barOrd
  apply List.countP_eq_zero.mpr
  intro x hx hb
  obtain ⟨j, -, hj⟩ := get_of_mem_take hx
  obtain ⟨pc, k⟩ := x
  cases k <;> simp only [Execution.isBarId, beq_iff_eq, reduceCtorEq] at hb
  rename_i id cnt m
  subst hb
  rcases corr_bar hpre hX ht hw hw' hj with ⟨-, rfl⟩ | ⟨-, -, st, -, hid⟩
  · cases m
    · rw [barEvents, List.countP_eq_zero] at h0
      exact absurd (h0 _ hx) (by simp [barIs])
    · rw [barEvents, List.countP_eq_zero] at h1
      exact absurd (h1 _ hx) (by simp [barIs])
  · omega

/-- **`TmemLifeFacts.corr_items`**: a correction thread's barrier-2 event of ordinal 1 (its end
barrier) follows one successful O-full poll of each stage per item of its cluster. -/
theorem TmemLifeFacts_corr_items {h b pc st I : Nat} {cnt : Option Nat} {m : BarMode}
    (_hh : h < L.threads) (hw : 8 ≤ warpOf L h) (hw' : warpOf L h < 12)
    (he : X.get (h, b) = some ⟨pc, .bar 2 cnt m⟩) (hb : barOrd X h b 2 = 1) (hst : st < 2)
    (hI : workOf L h I < totOf L) :
    I + 1 ≤ okPolls (oFullBar L (ctaOf L h) st) ((X.tr h).take b) := by
  rcases corr_origin hpre hX ht he hw hw' (fun _ _ h => by cases h) with ⟨p, -, hk⟩ |
    ⟨d, t, ins, o, -, hc, hi, -, -, -, hev⟩
  · cases hk
  obtain ⟨-, hk⟩ := hev (by simp)
  have hkw := corr_kOf hw hw'
  have hI' := (Correction.lt_items_iff (g := h) hpre).mpr hI
  have h1 := hc.oFull st hst
  rw [show oFullBar L (ctaOf L h) st = Correction.ownLoc L h (192 + 8 * st) by
    simp only [oFullBar, Correction.ownLoc, Correction.sb], h1]
  have hb2 := hc.bar2
  have hti := hi.tail
  have hst0 := hi.start
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  cases site <;> simp at hk
  · simp only [Correction.bar2Sync, Correction.bar2Arrive] at hb2
    rw [corr_barOrd2_zero hpre hX ht hw hw' hb2.1 hb2.2] at hb
    cases hb
  · omega
  · simp only at hti
    have := hti rfl (by simp) (by simp) (fun _ => by simp)
    simp only [Correction.oPos]
    omega

/-- **`OlderFacts.corr_stats_sync`**: a correction thread's sync on a statistics barrier is of an
item of its cluster. -/
theorem OlderFacts_corr_stats_sync {g j pc id : Nat} {cnt : Option Nat} (_hg : g < L.threads)
    (hw : 8 ≤ warpOf L g) (hw' : warpOf L g < 12) (he : X.IsBarrier (g, j) id cnt pc)
    (hid : id ≠ 2) :
    ∃ u, workOf L g u < totOf L ∧ barOrd X g j id < (kvBlocks P + 1) * (u + 1) := by
  rcases corr_origin hpre hX ht he hw hw' (fun _ _ h => by cases h) with ⟨p, -, hk⟩ |
    ⟨d, t, ins, o, -, hc, hi, -, -, -, hev⟩
  · cases hk
  obtain ⟨-, hk⟩ := hev (by simp)
  have hkw := corr_kOf hw hw'
  rw [corr_barOrd hpre hX ht hw hw' j hid, ← corr_trips_eq hpre]
  have htr := hi.trip
  have hit := hi.item
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  cases site <;> simp at hk
  case sync st gen =>
    obtain ⟨rfl, -, -⟩ := hk
    have hi' := hit rfl
    refine ⟨i, (Correction.lt_items_iff (g := g) hpre).mp hi', ?_⟩
    have hs := hc.sync st.val st.isLt
    rw [hs]
    simp only at htr
    fin_cases st <;> cases gen <;>
      simp [Correction.syncPos, Correction.Site.inTrip] at htr ⊢ <;> nlinarith
  all_goals exact absurd hk.1 hid

end

end
end PTX.Kernels.FlashAttn4Fwd.Proof
