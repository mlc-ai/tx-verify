-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Top.Prog.Classes
import Kernels.InklingRelDecode.Proof.Common.Export.TcClock
import Kernels.InklingRelDecode.Proof.Common.Export.TcLag
import Kernels.InklingRelDecode.Proof.Common.Export.TcForward
import Kernels.InklingRelDecode.Proof.Common.Export.TcCount
import Kernels.InklingRelDecode.Proof.Protocol.Tc.Agree
import Kernels.InklingRelDecode.Proof.Protocol.Shared.RescaleInduction
import Kernels.InklingRelDecode.Proof.Softmax.Export.RescaleChain
import Kernels.InklingRelDecode.Proof.Top.Safe.UbWeaken
import Kernels.InklingRelDecode.Proof.Lib.Dissent
import Lemmas.Flow.NthEv

/-! # A lane waiting at a collective `tcgen05` event steps

The lanes of a warp make their collective events in step: the `n`-th ones are at one pc
(`Protocol.Tc.tc_same_pc`). A lane that has made `c` of them (at most the waiting lane's `k`) has
the earlier events of the waiting lane's `c`-th, with one exception: a lane that decided the
rescale the other way is later than the lane at the O load. The decision agrees across the CTA
(`decision_agree`), so the exception does not occur. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX PTX.Flow PTX.Sched PTX.Tmem.Pair Protocol Protocol.Shared Protocol.Tc

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g h : Nat}

/-- The lanes' earlier collective events are at the same pcs. -/
private theorem same_pcs (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X) (sw : SameWarp L g h) (c : Nat) :
    ∀ n < c, ∀ {ix iy ex ey}, X.get (h, ix) = some ex → X.get (g, iy) = some ey →
      isTcColl ex = true → isTcColl ey = true → ((X.tr h).take ix).countP isTcColl = n →
      ((X.tr g).take iy).countP isTcColl = n → ex.pc = ey.pc := by
  intro n _ ix iy ex ey a b ta tb oa ob
  obtain ⟨pa, ka⟩ := ex
  obtain ⟨pb, kb⟩ := ey
  exact tc_same_pc hp hX hf safe (sameWarp_symm sw) a b ta tb (oa.trans ob.symm)

/-- Two lanes of a warp with as many earlier collective events have the same event counts. -/
private theorem same_counts (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X) (sw : SameWarp L g h) {t j c : Nat}
    (nuh : Frame.NoUbBefore X h t) (nug : Frame.NoUbBefore X g j)
    (oh : ((X.tr h).take t).countP isTcColl = c) (og : ((X.tr g).take j).countP isTcColl = c) :
    (∀ P ∈ Lib.dataPcs, ((X.tr h).take t).countP (fun e => e.pc == P) =
      ((X.tr g).take j).countP (fun e => e.pc == P)) ∧
    tmemOps ((X.tr h).take t) = tmemOps ((X.tr g).take j) := by
  have same := same_pcs hp hX hf safe sw c
  refine ⟨fun P hP => ?_, ?_⟩
  · rw [pc_count_tc hX nuh hP, pc_count_tc hX nug hP]
    refine tc_count_agree (fun e h => by simpa using (Bool.and_eq_true_iff.mp h).2) oh og ?_
    exact ord_same oh.ge og.ge same (fun _ _ tx ty h => by simp [h, tx, ty])
  · refine tc_count_agree (q := isTmemOp) (fun _ h => tmem_tc h) oh og ?_
    exact ord_same oh.ge og.ge same (fun {ix iy ex ey} a b tx ty h => by
      rw [tmem_pc hX a tx, tmem_pc hX b ty, h])

private theorem count_flat {u e} {p : Event → Bool} (get : X.get (g, u) = some e)
    (hp : p e = false) : ((X.tr g).take (u + 1)).countP p = ((X.tr g).take u).countP p := by
  rw [List.take_add_one, show (X.tr g)[u]? = some e from get, Option.toList_some,
    List.countP_append]
  simp [hp]

/-- **The lane at the O load of a rescale and a lane that decided the other way** cannot have the
same earlier collective events. -/
private theorem no_dissent (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X) (sw : SameWarp L g h) (nuh : NoUbLane X h)
    {j t c : Nat} {k : Kind} (gx : X.get (g, j) = some ⟨2260, k⟩) (tcx : isTcColl ⟨2260, k⟩ = true)
    (og : ((X.tr g).take j).countP isTcColl = c) (oh : ((X.tr h).take t).countP isTcColl = c)
    (dis : Lib.Dissent L X g j h t) : False := by
  have uni : ∀ {x kx ax bx cx rx okx}, X.get (x, kx) = some ⟨2255, .shfl .bfly ax bx cx rx okx⟩ →
      x % L.block < 128 → Uniform L X (x / L.block) (barOrdinal X x kx) := fun gs lane =>
    rescale_agree hp hX hf safe gs (fun _ => nofun) (by show Lib.afterFinal 2255 = 0; decide)
      (by show Lib.finalSync 2255 = false; decide) lane
  have lx := Export.tc_data_lane hp hX hf gx tcx
  have ly : h % L.block < 128 := by have := sw.2; omega
  rcases dis with ⟨v, a, b, c', r, ok, gv, skip, bars⟩ | ⟨u, kd, gu, ord⟩
  · obtain ⟨ux, ax, bx, cx, rx, okx, hux, gsx, skipF, cntx⟩ :=
      Softmax.Export.ldO_source hp hX gx (tc_false tcx)
    have uniX := uni gsx lx
    have uniY := uni gv ly
    have agree := decision_agree hp hX hf safe gsx gv lx ly sw.1.2.2.symm
      (by simp only [barOrdinal]; omega)
      (fun h' ch lh n' lt => uniX h' g ch lh rfl lx n' (by simp only [barOrdinal] at lt ⊢; omega))
      (fun h' ch lh n' lt => uniY h' h ch lh rfl ly n' (by simp only [barOrdinal] at lt ⊢; omega))
    rw [skipF, skip] at agree
    exact Bool.noConfusion agree
  · have tcu : isTcColl ⟨2329, kd⟩ = true := by
      rw [Lib.tcColl_event hX gu (nuh.kind gu)]
      simp [Lib.dataPcs]
    obtain ⟨jc, ec, hjc, gc, tcc, occ⟩ := exists_nthEv (X := X) (p := isTcColl) (g := g) (k := j)
      (n := c - 1) (by omega)
    obtain ⟨pe, ke⟩ := ec
    have pc : pe = 2329 := (same_pcs hp hX hf safe sw c (c - 1) (by omega) gu gc tcu tcc
      (by omega) occ).symm
    subst pc
    have nub := Frame.noUbBefore_of_get hX gx
    have len : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp gx).1
    rcases Nat.lt_or_ge (jc + 1) j with lt1 | ge1
    · obtain ⟨e1, g1⟩ : ∃ e, X.get (g, jc + 1) = some e :=
        ⟨_, List.getElem?_eq_getElem (show jc + 1 < (X.tr g).length by omega)⟩
      obtain ⟨p1, nxt⟩ := Export.after_waitStO hp hX hf gc (tc_false tcc) g1 (nub _ lt1 _ g1)
      have tc1 : isTcColl e1 = false := by
        rw [Lib.tcColl_event hX g1 (nub _ lt1 _ g1)]
        cases hm : isTmemOp e1
        · simp [p1, Lib.dataPcs]
        · have := Export.tmem_event_pc hX g1 hm
          simp [Lib.resPcs, p1] at this
      obtain ⟨e2, g2⟩ : ∃ e, X.get (g, jc + 2) = some e :=
        ⟨_, List.getElem?_eq_getElem (show jc + 2 < (X.tr g).length by omega)⟩
      rcases Nat.lt_or_ge (jc + 2) j with lt2 | ge2
      · have p2 := nxt e2 g2 (nub _ lt2 _ g2)
        have tc2 : isTcColl e2 = true := by
          rw [Lib.tcColl_event hX g2 (nub _ lt2 _ g2), p2]
          simp [Lib.dataPcs]
        have a1 := countP_take_succ (p := isTcColl) gc tcc
        have a2 := count_flat (p := isTcColl) g1 tc1
        have := nthEv_unique (p := isTcColl) gx tcx g2 tc2 (by
          rw [show jc + 2 = jc + 1 + 1 from rfl, a2, a1]
          omega)
        omega
      · obtain rfl : j = jc + 2 := by omega
        have p2 := nxt _ gx (tc_false tcx)
        change 2260 = 1009 at p2
        omega
    · obtain rfl : j = jc + 1 := by omega
      have := (Export.after_waitStO hp hX hf gc (tc_false tcc) gx (tc_false tcx)).1
      change 2260 = 999 at this
      omega

/-- **A lane with at most the collective events of the waiting lane is no later than it**, and
strictly earlier when its event is not collective or it has made fewer. -/
private theorem lag_gen (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X) (hg : g < L.threads) (hh : h < L.threads)
    (sw : SameWarp L g h) (nug : NoUbLane X g) (nuh : NoUbLane X h) {j k t : Nat}
    (hk : X.TcK (g, j) k) (ht : t ≤ (X.tr h).length) (hal : Export.TcAlive Q L X h t)
    (hc : ((X.tr h).take t).countP isTcColl ≤ k) :
    timeAt (schedule Q L) X h t ≤ timeAt (schedule Q L) X g j ∧
    (∀ e, X.get (h, t) = some e → isTcColl e = false →
      timeAt (schedule Q L) X h t < timeAt (schedule Q L) X g j) ∧
    (((X.tr h).take t).countP isTcColl < k →
      timeAt (schedule Q L) X h t < timeAt (schedule Q L) X g j) := by
  obtain ⟨⟨⟨pc, kd⟩, he, tc⟩, hjk⟩ := hk
  have hjk : ((X.tr g).take j).countP isTcColl = k := hjk
  obtain ⟨jE, eE, hjE, gE, tcE, oE, strict⟩ : ∃ jE eE, jE ≤ j ∧ X.get (g, jE) = some eE ∧
      isTcColl eE = true ∧ ((X.tr g).take jE).countP isTcColl =
        ((X.tr h).take t).countP isTcColl ∧
      (((X.tr h).take t).countP isTcColl < k → jE < j) := by
    by_cases hck : ((X.tr h).take t).countP isTcColl = k
    · exact ⟨j, ⟨pc, kd⟩, le_rfl, he, tc, hjk.trans hck.symm, by omega⟩
    · obtain ⟨jE, eE, hlt, gE, tcE, oE⟩ := exists_nthEv (X := X) (p := isTcColl) (g := g)
        (k := j) (n := ((X.tr h).take t).countP isTcColl) (by omega)
      exact ⟨jE, eE, hlt.le, gE, tcE, oE, fun _ => hlt⟩
  obtain ⟨vp, vt⟩ := same_counts hp hX hf safe sw (nuh.before t) (nug.before jE) rfl oE
  have mono : timeAt (schedule Q L) X g jE ≤ timeAt (schedule Q L) X g j ∧
      (jE < j → timeAt (schedule Q L) X g jE < timeAt (schedule Q L) X g j) := by
    rcases Nat.lt_or_ge jE j with lt | ge
    · obtain ⟨pE, kE⟩ := eE
      have := Export.tc_time_lt hp hX hf nug hg gE he tcE tc lt
      exact ⟨this.le, fun _ => this⟩
    · obtain rfl : jE = j := le_antisymm hjE ge
      exact ⟨le_rfl, fun h => absurd h (lt_irrefl _)⟩
  obtain ⟨pE, kE⟩ := eE
  rcases Export.tc_lag_at hp hX hf nuh hg hh sw gE tcE ht hal vp vt with ⟨l1, l2⟩ | ⟨p2260, dis⟩
  · exact ⟨l1.trans mono.1, fun e he' nc => (l2 e he' nc).trans_le mono.1,
      fun lt => l1.trans_lt (mono.2 (strict lt))⟩
  · subst p2260
    exact (no_dissent hp hX hf safe sw nuh gE tcE oE rfl dis).elim

/-- **A lane of the warp with at most the collective events of a waiting lane is no later than
its event.** -/
public theorem Prog.tc_lag (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (safe : ¬Race L X) (hu : ¬ HasUb X) {g h j k : Nat} (hg : g < L.threads)
    (hh : h < L.threads) (sw : SameWarp L g h) (hk : X.TcK (g, j) k)
    (hle : (X.tr h).countP isTcColl ≤ k) :
    threadTime (schedule Q L) X h ≤ timeAt (schedule Q L) X g j := by
  have lag := fun {t : Nat} => lag_gen hp hX hf safe hg hh sw (.of_noUb hu g) (.of_noUb hu h) hk
    (t := t)
  rw [Sched.threadTime_eq_timeAt]
  rcases Export.tc_time_cases hf hh (X.tr h).length with hal | h0 | ⟨hpos, hal, hteq⟩
  · exact (lag le_rfl hal (by rwa [List.take_length])).1
  · rw [h0]; exact Nat.zero_le _
  · obtain ⟨-, l2, l3⟩ := lag (by omega) hal (
      (le_trans (List.take_sublist _ _).countP_le hle))
    obtain ⟨ev, gev⟩ : ∃ ev, X.get (h, (X.tr h).length - 1) = some ev :=
      ⟨_, List.getElem?_eq_getElem (show (X.tr h).length - 1 < (X.tr h).length by omega)⟩
    rw [hteq]
    by_cases tcl : isTcColl ev = true
    · have step := countP_take_succ (p := isTcColl) gev tcl
      rw [Nat.sub_add_cancel hpos, List.take_length] at step
      have := l3 (by omega)
      omega
    · have := l2 ev gev (by simpa using tcl)
      omega


/-- **A lane waiting at a collective `tcgen05` event steps**: the lanes of its warp that have not
made it are no later, and its clock rises after it. -/
public theorem Prog.tc_steps (hp : Pre Q L m) (hs : SafeGoal kernel Assumptions.all L m)
    (hmax : Maximal L kernel Assumptions.all m X) (hf : Follow Q L X) {g : Nat}
    (hpd : Frame.Pending L X g) (hrel : ¬ Step.Released L X g) (hw : Sched.TcWait L X g) :
    Sched.Steps (schedule Q L) m X (.thread g) := by
  have hX := hmax.1
  have hsafe := hs.2 X hX
  have safe : ¬Race L X := fun h => hsafe (by simp [Unsafe, h])
  have hu : ¬ HasUb X := Sched.safe_noUb hsafe
  refine Export.tc_steps hp hs hmax hf (fun {g h j k} hg hh sw hk hle => ?_)
    (fun {g j k} hg hk => ?_) hpd hrel hw
  · exact Prog.tc_lag hp hX hf safe hu hg hh sw hk hle
  · obtain ⟨⟨⟨pc, kd⟩, he, tc⟩, -⟩ := hk
    exact Export.tc_after hp hX hf hg he tc
