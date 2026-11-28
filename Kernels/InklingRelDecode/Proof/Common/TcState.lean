-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.EndTime
public import Kernels.InklingRelDecode.Proof.Softmax.Export.TcNext
public import Kernels.InklingRelDecode.Proof.Epilogue.Export.TcNext
public import Lemmas.Flow.GlueStep
import all Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.Export.TcCount
public import Kernels.InklingRelDecode.Proof.Common.TcCount

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.TcState
open PTX PTX.Flow PTX.Proof PTX.Sched PTX.Tmem.Pair
variable {Q : Params} {L : Launch} {g : Nat}
def SoftEpi {Q L g} (s : (thread Q L g).D) : Prop :=
  (∃ w ent d n, s = softState w ent d n) ∨ ∃ w ent d n, s = epiState w ent d n
theorem soft_fwd {w ent d n ev s'} (hi : Softmax.Control.Inv ent (g % L.block) d)
    (step : (thread Q L g).next (softState w ent d n) ev = some (some s')) :
    SoftEpi s' ∧ siteTime (Q := Q) (L := L) (g := g) (softState w ent d n) ≤ siteTime s' ∧
      (d.site.pc ∈ Lib.loopTcPcs ∨ d.site.pc ∈ Lib.loopBarPcs →
        siteTime (Q := Q) (L := L) (g := g) (softState w ent d n) < siteTime s') := by
  obtain ⟨s1, cnt⟩ := s'
  obtain ⟨p1, m1, rfl⟩ := Code.glue_inr_some (Code.counted_next_some step).1
  obtain ⟨p2, m2, rfl⟩ := Code.glue_inr_some m1
  obtain ⟨dn, m3, rfl⟩ := Code.glue_inl_some m2
  have tn := Softmax.Export.time_next hi m3
  by_cases hs : dn.site = .epilogue
  · rw [Code.enter_some (show epiExit dn = some () by simp [epiExit, hs])]
    change SoftEpi (epiState w ent {} cnt) ∧ siteTime (softState w ent d n) ≤
      siteTime (epiState w ent {} cnt) ∧
      (_ → siteTime (softState w ent d n) < siteTime (epiState w ent {} cnt))
    simp only [siteTime_soft, siteTime_epi]
    obtain ⟨s, i, v⟩ := dn
    simp only at hs
    subst hs
    exact ⟨.inr ⟨_, _, _, _, rfl⟩, tn⟩
  · rw [Code.enter_none (show epiExit dn = none by simp [epiExit, hs])]
    change SoftEpi (softState w ent dn cnt) ∧ siteTime (softState w ent d n) ≤
      siteTime (softState w ent dn cnt) ∧
      (_ → siteTime (softState w ent d n) < siteTime (softState w ent dn cnt))
    simp only [siteTime_soft]
    exact ⟨.inl ⟨_, _, _, _, rfl⟩, tn⟩
theorem epi_fwd {w ent d n ev s'}
    (step : (thread Q L g).next (epiState w ent d n) ev = some (some s')) :
    SoftEpi s' ∧ siteTime (Q := Q) (L := L) (g := g) (epiState w ent d n) ≤ siteTime s' ∧
      ((d.site.pc = 2607 ∨ d.site.pc = 2608 ∨ d.site.pc = 2851 ∨
        d.site.pc = 2846 ∨ d.site.pc = 2849 ∨ d.site.pc = 2850) →
        siteTime (Q := Q) (L := L) (g := g) (epiState w ent d n) < siteTime s') := by
  obtain ⟨s1, cnt⟩ := s'
  obtain ⟨p1, m1, rfl⟩ := Code.glue_inr_some (Code.counted_next_some step).1
  obtain ⟨p2, m2, rfl⟩ := Code.glue_inr_some m1
  obtain ⟨dn, m3, rfl⟩ := Code.glue_inr_some m2
  change SoftEpi (epiState w ent dn cnt) ∧ siteTime (epiState w ent d n) ≤
    siteTime (epiState w ent dn cnt) ∧
    (_ → siteTime (epiState w ent d n) < siteTime (epiState w ent dn cnt))
  simp only [siteTime_epi]
  exact ⟨.inr ⟨_, _, _, _, rfl⟩, Epilogue.Export.time_next m3⟩
theorem step_of {X t ev} {s s1 : (thread Q L g).D}
    (get : (X.tr g)[t]? = some ev) (hs : Frame.stateAt (thread Q L) X g t = some (some s))
    (hs1 : Frame.stateAt (thread Q L) X g (t + 1) = some (some s1)) :
    (thread Q L g).next s ev = some (some s1) := by
  have := Frame.stateAt_succ (C := thread Q L) get
  rw [hs, hs1] at this
  exact this.symm
section Env
variable {m : Mem0} {X : Execution} (hp : Pre Q L m)
  (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
include hp hX hf
theorem coll_state {j pc k} (he : X.get (g, j) = some ⟨pc, k⟩) (tc : isTcColl ⟨pc, k⟩ = true) :
    ∃ s : (thread Q L g).D, Frame.stateAt (thread Q L) X g j = some (some s) ∧
      TcInv s ∧ (thread Q L g).inv s ∧ Frame.NoUbBefore X g j ∧
      ((∃ st n, s = (.inl st, n) ∧ pc = st.site.pc ∧ (pc = 11 ∨ pc = 15)) ∨
       (∃ w ent d n, s = softState w ent d n ∧ pc = d.site.pc ∧ pc ∈ Lib.loopTcPcs) ∨
       (∃ w ent d n, s = epiState w ent d n ∧ pc = d.site.pc ∧
         (pc = 2607 ∨ pc = 2608 ∨ pc = 2851))) := by
  have nu : ∀ f, (⟨pc, k⟩ : Event).kind ≠ .ub f := by
    intro f h
    change k = .ub f at h
    subst h
    simp [isTcColl] at tc
  have hg := Frame.lt_of_get hX he
  obtain ⟨s, hs, -⟩ := Frame.good_stateU (fun g h => thread_sound hp h) hX he
    (fun _ f h => nu f (congrArg Event.kind h)) (hf g hg j)
  have nub := Frame.noUbBefore_of_get hX he
  have hpc : pc = (thread Q L g).pc s :=
    Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hs nu
  have hk := (List.getElem?_eq_some_iff.mp he).1.le
  have tbl := reached_table hf hg nub hs
  have pl := state_role s
  rw [← hpc] at pl
  refine ⟨s, hs, tc_inv hp hX hf hg hk hs nub, tbl.1, nub, ?_⟩
  have inv := tbl.1
  have loop (h : pc ∈ Lib.loopTcPcs) : 574 < pc ∧ pc < 2331 := by
    simp only [Lib.loopTcPcs, List.mem_cons, List.not_mem_nil, or_false] at h
    omega
  have epi (h : pc = 2607 ∨ pc = 2608 ∨ pc = 2851) : 2565 ≤ pc ∧ pc < 2853 := by omega
  rcases Export.tc_pc_where hp hX hf he tc with h | h | h | h | h | h
  · obtain ⟨st, n, rfl⟩ := pl.startup (by omega)
    exact .inl ⟨st, n, rfl, hpc, .inl h⟩
  · obtain ⟨st, n, rfl⟩ := pl.startup (by omega)
    exact .inl ⟨st, n, rfl, hpc, .inr h⟩
  · obtain ⟨w, ent, d, n, rfl⟩ := pl.softmax (loop h).1 (loop h).2
    exact .inr (.inl ⟨w, ent, d, n, rfl, hpc, h⟩)
  all_goals
    obtain ⟨w, ent, d, n, rfl⟩ := pl.epilogue (epi (by omega)).1 (epi (by omega)).2 inv
    exact .inr (.inr ⟨w, ent, d, n, rfl, hpc, by omega⟩)
theorem next_of {t} (hg : g < L.threads) (hu : NoUbLane X g) {s : (thread Q L g).D}
    (hs : Frame.stateAt (thread Q L) X g t = some (some s)) (hlen : t + 1 < (X.tr g).length) :
    ∃ s1, Frame.stateAt (thread Q L) X g (t + 1) = some (some s1) ∧
      (thread Q L g).next s (X.tr g)[t] = some (some s1) := by
  have get : (X.tr g)[t]? = some (X.tr g)[t] := List.getElem?_eq_getElem (by omega)
  have get' : X.get (g, t + 1) = some (X.tr g)[t + 1] := List.getElem?_eq_getElem hlen
  obtain ⟨s2, hs2, -⟩ := Frame.good_stateU (fun g h => thread_sound hp h) hX get'
    (fun _ f h => hu.kind get' f (congrArg Event.kind h)) (hf g hg (t + 1))
  exact ⟨s2, hs2, step_of get hs hs2⟩
theorem chain {j} (hu : NoUbLane X g) (hg : g < L.threads) {s : (thread Q L g).D}
    (hs : Frame.stateAt (thread Q L) X g j = some (some s)) (se : SoftEpi s) {j' : Nat}
    (hj : j ≤ j') : j' < (X.tr g).length → ∃ s' : (thread Q L g).D,
      Frame.stateAt (thread Q L) X g j' = some (some s') ∧ SoftEpi s' ∧
        siteTime s ≤ siteTime s' := by
  induction j', hj using Nat.le_induction with
  | base => exact fun _ => ⟨s, hs, se, Nat.le_refl _⟩
  | succ t ht ih =>
    intro hlen
    obtain ⟨s1, hs1, se1, le1⟩ := ih (by omega)
    obtain ⟨s2, hs2, step⟩ := next_of hp hX hf hg hu hs1 hlen
    have get : (X.tr g)[t]? = some (X.tr g)[t] := List.getElem?_eq_getElem (by omega)
    have tbl := reached_table hf hg (Frame.noUbBefore_of_get hX get) hs1
    refine ⟨s2, hs2, ?_⟩
    rcases se1 with ⟨w, ent, d, n, rfl⟩ | ⟨w, ent, d, n, rfl⟩
    · obtain ⟨se2, le2, -⟩ := soft_fwd tbl.1.1 step
      exact ⟨se2, Nat.le_trans le1 le2⟩
    · obtain ⟨se2, le2, -⟩ := epi_fwd step
      exact ⟨se2, Nat.le_trans le1 le2⟩
theorem coll_after {j pc k} (he : X.get (g, j) = some ⟨pc, k⟩) (tc : isTcColl ⟨pc, k⟩ = true)
    {s : (thread Q L g).D}
    (hs : Frame.stateAt (thread Q L) X g j = some (some s)) {s1 : (thread Q L g).D}
    (hs1 : Frame.stateAt (thread Q L) X g (j + 1) = some (some s1)) :
    siteTime s < siteTime s1 ∧ (SoftEpi s → SoftEpi s1) := by
  obtain ⟨s0, hs0, -, -, nub, cls⟩ := coll_state hp hX hf he tc
  rw [hs] at hs0
  cases hs0
  have step := step_of he hs hs1
  rcases cls with ⟨st, n, rfl, hpc, hpc2⟩ | ⟨w, ent, d, n, rfl, hpc, hl⟩ |
      ⟨w, ent, d, n, rfl, hpc, hl⟩
  · rw [next_start] at step
    rcases hsu : Startup.succ L g st ⟨pc, k⟩ with _ | _ | st' <;> rw [hsu] at step <;>
      simp only [Option.map_some, Option.map_none, reduceCtorEq, Option.some.injEq] at step
    have hx : Startup.enterOf st' = none := by
      obtain ⟨sit, tm, x, w⟩ := st
      cases sit <;> simp [Startup.Site.pc] at hpc <;> simp [Startup.succ] at hsu <;>
        first | (exfalso; omega) | (subst hsu; first | rfl | (split_ifs <;> rfl))
    rw [enter_inl hx] at step
    subst step
    refine ⟨?_, fun h => ?_⟩
    · exact siteTime_startup_succ _ _ (by omega) hsu
    · rcases h with ⟨w, ent, d, n', h⟩ | ⟨w, ent, d, n', h⟩ <;> cases h
  · obtain ⟨se, lt, hlt⟩ := soft_fwd (reached_table hf (Frame.lt_of_get hX he) nub hs).1.1 step
    exact ⟨hlt (.inl (hpc ▸ hl)), fun _ => se⟩
  · obtain ⟨se, lt, hlt⟩ := epi_fwd step
    exact ⟨hlt (by rcases hl with h | h | h <;> simp [← hpc, h]), fun _ => se⟩
end Env
theorem tracked_ne {X : Execution} (hf : Follow Q L X) (hg : g < L.threads) (k : Nat) :
    Frame.stateAt (thread Q L) X g k ≠ some none := (hf g hg k).1
end PTX.Kernels.InklingRelDecode.Proof.TcState
