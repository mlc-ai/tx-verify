-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.WarpFacts
public import Lemmas.Step.WarpElect
public import Lemmas.Step.WarpBar
public import Lemmas.Step.SetMaxNReg
public import Kernels.InklingRelDecode.Proof.Interface.PwBar
public import Lemmas.CtaBarrier.CtaBarrierIdentity
public import Lemmas.CtaBarrier.CtaBarrierFault
public import Lemmas.Protocol.NamedBarArrive
public import Lemmas.Step.ExitLast
public import Lemmas.Tmem.TmemPairHistory
public import Kernels.InklingRelDecode.Proof.Progress.Alloc

@[expose] public section

/-! # The lanes of a warp at one warp collective

When every lane of a warp is at its `n`-th warp collective, each lane is released when one is
(`lane_released`): its last event never blocks, or it is the synchronizing event that the warp
and the ordinal fix (`WarpCollFacts.last`), which the released lane has also made, and which is
ready there (the last event of a released lane, or an earlier one, returned, `ready_at`). The
readiness carries over (`released_of_sync`): a register request of the same ordinal and operands
(`SetMaxNReg.ready_of_sameRequest`); a warp-collective `tcgen05` event of the same ordinal, which
every lane has made (`Sched.tc_ready_of_done`), or, for a `cta_group::1` allocator operation,
whose request is performed and complete and, for an allocation, whose warp has stored the address
(`ready_res_lane`, `AllocStored`); a `bar.sync` of the same barrier and ordinal on it, which is in
the record of the released lane's arrival and so in its done generation (`ready_bar_lane`). The
warp then performs one instance of the collective (`WarpColl.lean`, `Sched.coll_batch`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress

open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface Classical

noncomputable section

variable {T : Nat → TSt → Nat} {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A thread whose last event, if any, never blocks is released. -/
theorem released_of_free {h : Nat} (hf : LastFree X h) : Step.Released L X h := by
  cases hq : X.get (h, (X.tr h).length - 1) with
  | none =>
    have h0 : X.tr h = [] := by
      by_contra hne
      have hlt : (X.tr h).length - 1 < (X.tr h).length := by
        have := List.length_pos_of_ne_nil hne
        omega
      have : X.get (h, (X.tr h).length - 1) ≠ none := by
        simp [Execution.get, List.getElem?_eq_getElem hlt]
      exact this hq
    exact Sched.released_nil h0
  | some q => exact Sched.released_of_unblocking hq (hf q hq)

/-- **An event of a released thread that blocks until it is ready is ready**: the last one by
`Step.Released`, an earlier one because it has returned (DEP-ORDER). -/
theorem ready_at (hX : Consistent L kernel asms mem0 X) {g j pc : Nat} {k : Kind}
    (hrel : Step.Released L X g) (hj : X.get (g, j) = some ⟨pc, k⟩)
    (hk : k.resume = .blocking false) : Ready L X (g, j) := by
  have hlt : j < (X.tr g).length := len_of_get hj
  by_cases hl : j + 1 < (X.tr g).length
  · apply hX.dependency.ready
    have hw : ∀ m v ok a b, k ≠ .wait m v ok a b := by
      rintro m v ok a b rfl
      simp [Kind.resume] at hk
    unfold Returned
    rw [hj]
    split
    · rename_i heq
      simp only [Option.some.injEq, Event.mk.injEq] at heq
      exact absurd heq.2 (hw _ _ _ _ _)
    · rename_i heq
      obtain rfl := Option.some.inj heq
      simp only [hk]
      exact hl
    · rename_i heq
      cases heq
  · have : j = (X.tr g).length - 1 := by omega
    subst this
    exact hrel.ready _ _ hj hk

/-! ### Readiness carried between two lanes of one instance -/

/-- **A `bar.sync` of a lane of the warp of a ready `bar.sync`, of the same barrier and ordinal on
it, at the end of its trace, is ready**: the ready one's record holds an arrival of every live
lane of the warp, of the record's ordinal, which is the lane's last event; its generation is the
ready one's, which is done. -/
theorem ready_bar_lane (hX : Consistent L kernel asms mem0 X) {g h j b o pcg pch : Nat}
    {c c' : Option Nat} (hs : SameWarp L g h) (hr : Ready L X (g, j))
    (hgj : X.IsBarrier (g, j) b c pcg)
    (hog : ((X.tr g).take j).countP (Execution.isBarId b) = o)
    (hh : X.IsBarrier (h, (X.tr h).length - 1) b c' pch)
    (hoh : ((X.tr h).take ((X.tr h).length - 1)).countP (Execution.isBarId b) = o) :
    Ready L X (h, (X.tr h).length - 1) := by
  have hg : g < L.threads := hs.1.1
  have hht : h < L.threads := hs.1.2.1
  have hcta : g / L.block = h / L.block := hs.1.2.2
  have hb : 0 < L.block := NamedBar.block_pos_of_thread_lt hg
  have hc : g / L.block < L.grid := (Nat.div_lt_iff_lt_mul hb).mpr hg
  obtain ⟨-, hsrcs, last, hlast⟩ := hX.ctaBar.2 _ hc
  have hgj' : X.get (g, j) = some ⟨pcg, .bar b c .sync⟩ := hgj
  have hh' : X.get (h, (X.tr h).length - 1) = some ⟨pch, .bar b c' .sync⟩ := hh
  -- the release of `g`'s generation
  have hmc : Need.cond (∃ key, CtaBarK L X (g, j) key ∧ CtaBarDone L X ((g, j).1 / L.block) key) ∈
      Needs L X (g, j) := by
    simp only [Needs, hgj', KindNeeds, ctaBarNeeds]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨key, hk, hd⟩ := hr _ hmc
  -- the record of `g`'s arrival, and `h`'s event in it
  have hmw : Need.node (fun x => ∃ i, ∃ r : CtaBarrier.Record EvId, ∃ y,
      (X.barriers ((g, j).1 / L.block))[i]? = some r ∧ (g, j) ∈ r.refs ∧ x = .thread y ∧
      y.1 = h ∧ (y ∈ r.refs ∨ ∃ (j' g' : Nat), j' < i ∧
        (X.barriers ((g, j).1 / L.block))[j']? = some (CtaBarrier.Record.exit g' y))) ∈
      Needs L X (g, j) := by
    simp only [Needs, hgj', KindNeeds, ctaBarNeeds]
    exact List.mem_append_left _ (List.mem_map.mpr
      ⟨h, mem_warpLanes_of_sameWarp (sameWarp_symm hs), rfl⟩)
  obtain ⟨x, -, i, r, y, hri, hgr, rfl, hy1, hy⟩ := hr _ hmw
  simp only at hri hgr
  have hlen : 0 < (X.tr h).length := by
    have := len_of_get hh'
    simp only at this
    omega
  have hyl : y ∈ r.refs := by
    rcases hy with hy | ⟨j', g', -, hj'⟩
    · exact hy
    · exfalso
      obtain ⟨-, -, pcx, hx⟩ := hsrcs _ (List.mem_of_getElem? hj')
      have hyt : y.1 < L.threads := hy1 ▸ hht
      have := Execution.exit_last hX hyt hx
      obtain ⟨y1, y2⟩ := y
      simp only at hy1 this
      subst hy1
      have hy2 : y2 = (X.tr y1).length - 1 := by omega
      rw [hy2, hh'] at hx
      cases hx
  cases r with
  | exit g0 y0 =>
    exfalso
    obtain ⟨-, -, pcx, hx⟩ := hsrcs _ (List.mem_of_getElem? hri)
    simp only [CtaBarrier.Record.refs, List.mem_singleton] at hgr
    rw [← hgr, hgj'] at hx
    cases hx
  | arrival id w cnt lanes =>
    obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hgr
    obtain ⟨q', hq', hqe'⟩ := List.mem_map.mp hyl
    obtain ⟨s, t, hat, hp⟩ := CtaBarrier.run_at_record hlast hri
    obtain ⟨-, -, -, ⟨pq, mq, hbq⟩, hordq, -⟩ := NamedBar.record_ordinal hX hc hlast hri hat hq
    obtain ⟨-, -, -, ⟨pq', mq', hbq'⟩, hordq', -⟩ :=
      NamedBar.record_ordinal hX hc hlast hri hat hq'
    rw [hqe, hgj'] at hbq
    simp only [Option.some.injEq, Event.mk.injEq, Kind.bar.injEq] at hbq
    obtain ⟨-, rfl, -, -⟩ := hbq
    rw [hqe'] at hbq' hordq'
    rw [hqe] at hordq
    obtain ⟨y1, y2⟩ := y
    simp only at hy1
    subst hy1
    simp only at hordq hordq'
    -- `h`'s arrival in the record is its last event
    have hy2 : y2 = (X.tr y1).length - 1 := by
      obtain ⟨evy, hevy⟩ : ∃ ev, (X.tr y1)[y2]? = some ev := ⟨_, hbq'⟩
      have hby : Execution.isBarId b evy = true := by
        have : X.get (y1, y2) = some evy := hevy
        rw [hbq'] at this
        cases this
        simp [Execution.isBarId]
      exact NamedBar.ordinal_unique hevy hh' hby (by simp [Execution.isBarId])
        (by rw [← hordq', hordq, hog, hoh])
    subst hy2
    -- its generation is the ready one's
    have hgen_g := generationOf_of_record hri hat hp hq
    rw [hqe] at hgen_g
    have hgen_h := generationOf_of_record hri hat hp hq'
    rw [hqe'] at hgen_h
    obtain ⟨hid, hph⟩ := CtaBarrier.GenerationOf.unique (hX.ctaBar.2 _ hc).1 hgen_g hk.2.2
    have hkh : CtaBarK L X (y1, (X.tr y1).length - 1) key := by
      refine ⟨hht, ⟨c', pch, ?_⟩, ?_⟩
      · rw [← hid]; exact hh
      · show CtaBarrier.GenerationOf L.block (X.barriers (y1 / L.block)) _ _ _
        rw [← hcta, ← hid, ← hph]
        exact hgen_h
    have hdh : CtaBarDone L X ((y1, (X.tr y1).length - 1).1 / L.block) key := by
      show CtaBarDone L X (y1 / L.block) key
      rw [← hcta]
      exact hd
    exact NamedBar.ready_of_released hX.ctaBar hh' hkh hdh

/-- A lane of a valid allocator request is a lane of every request with another lane of its
warp-collective instance. -/
theorem participates_of_tcK {w : Tmem.Pair.WarpRequest} {grp : CtaGroup}
    (hv : w.Valid L X grp) {e f : EvId} {k : Nat} (hp : Tmem.Pair.Participates L w e)
    (hk : X.TcK e k) (hs : SameWarp L e.1 f.1) (hf : X.TcK f k) :
    Tmem.Pair.Participates L w f := by
  obtain ⟨l0, rfl⟩ := hp
  obtain ⟨k', hk'⟩ := hv.2.2.2
  have hkk : k' = k := (hk' l0).2.symm.trans hk.2
  obtain ⟨p1, p2, -⟩ := Tmem.Pair.WarpRequest.event_props hv l0
  have hcta : f.1 / L.block = w.cta := by rw [← hs.1.2.2, p1]
  have hwarp : f.1 % L.block / 32 = w.warp := by rw [← hs.2, p2]
  let l : Fin 32 := ⟨f.1 % L.block % 32, Nat.mod_lt _ (by decide)⟩
  have heq : w.event L l = (f.1, w.indices l) := by
    have e1 := Nat.div_add_mod f.1 L.block
    have e2 := Nat.div_add_mod (f.1 % L.block) 32
    rw [hcta] at e1
    rw [hwarp] at e2
    show (w.cta * L.block + w.warp * 32 + f.1 % L.block % 32, w.indices l) = (f.1, w.indices l)
    rw [Nat.mul_comm w.cta]
    congr 1
    omega
  have hl := hk' l
  rw [heq, hkk] at hl
  obtain ⟨f1, f2⟩ := f
  have := Execution.TcK.unique hl hf
  simp only at this heq
  exact ⟨l, by rw [heq, this]⟩

/-- **An allocator operation of a lane of the warp of a ready `cta_group::1` allocator operation,
of the same instance, is ready**: its request is the ready one's, performed and complete; for an
allocation of a lane other than lane 0, the warp's address store is the ready lane's result, or,
when the ready lane is lane 0, its next event (`hpub`, EXT-TMEM-ALLOC-RESULT-ORDER). -/
theorem ready_res_lane (hX : Consistent L kernel asms mem0 X) {g h j l k pc : Nat}
    {dst : Option Loc} {act : Tmem.Request} (hs : SameWarp L g h) (hr : Ready L X (g, j))
    (hg : X.get (g, j) = some ⟨pc, .tc (.resource .one dst act)⟩) (hgk : X.TcK (g, j) k)
    (hhk : X.TcK (h, l) k)
    (hpub : ∀ n, act = .alloc n → laneOf L g = 0 → ∃ e, X.get (g, j + 1) = some e ∧
      ∃ D bytes, dst = some D ∧ D.space = .shared ∧ D.cta = g / L.block ∧
        e = ⟨pc, .wr { loc := D, size := 4 } bytes⟩) : Ready L X (h, l) := by
  have hv := hX.tmemPair
  have hnd : Needs L X (g, j) = resourceNeeds L X (g, j) .one act := by
    simp only [Needs, hg]
    rfl
  obtain ⟨cta, r, hrm, hpg⟩ : Tmem.Pair.Performed L X (g, j) :=
    hr (.cond (Tmem.Pair.Performed L X (g, j))) (by rw [hnd]; simp [resourceNeeds])
  have hrv := ((hv.1 cta).1 r hrm).2.2
  have hph : Tmem.Pair.Participates L r.own (h, l) := participates_of_tcK hrv hpg hgk hs hhk
  have hcov : Tmem.Pair.Covered L X (g, j) := by
    have hm : Tmem.Pair.MustWait X (g, j) := ⟨pc, .one, dst, act, hg, by cases act <;> simp⟩
    exact hr (.cond (Tmem.Pair.Covered L X (g, j)))
      (by rw [hnd]; simp [resourceNeeds, needsIf, hm])
  obtain ⟨ws, hws, w, hw, hpw⟩ := hcov
  obtain ⟨grp, hwv⟩ := hws.valid hv hw
  have hcovh : Tmem.Pair.Covered L X (h, l) := ⟨ws, hws, w, hw,
    participates_of_tcK hwv hpw hgk hs hhk⟩
  obtain ⟨l0, hl0⟩ := hpg
  obtain ⟨l1, hl1⟩ := hph
  have hgh : X.get (h, l) = some ⟨pc, .tc (.resource .one dst act)⟩ := by
    rw [← hl1, hrv.2.2.1 l1, ← hrv.2.2.1 l0, hl0, hg]
  have hndh : Needs L X (h, l) = resourceNeeds L X (h, l) .one act := by
    simp only [Needs, hgh]
    rfl
  have hall := hrv.tcDone ⟨l0, hl0⟩ hgk
  intro n hn
  rw [hndh] at hn
  unfold resourceNeeds at hn
  rcases List.mem_append.mp hn with hn | hn
  swap
  · have hnode := Tmem.Pair.allocResultNeeds_node L hn
    subst hnode
    cases act with
    | alloc nc =>
      have hlh : laneOf L h ≠ 0 := by
        intro h0
        simp [Tmem.Pair.allocResultNeeds, h0] at hn
      have hcta : g / L.block = h / L.block := hs.1.2.2
      by_cases hg0 : laneOf L g = 0
      · obtain ⟨e, he1, D, bytes, rfl, hDs, hDc, rfl⟩ := hpub nc rfl hg0
        exact ⟨.thread (g, j + 1), ⟨_, he1⟩, D, hs, hg0, hDs, hDc.trans hcta, j, pc, .one, nc, k,
          bytes, rfl, hg, hgh, hgk, hhk, he1⟩
      · obtain ⟨x, hxp, hfill⟩ := hr (.node (Tmem.Pair.AllocResultFill L X (g, j)))
          (by rw [hnd]; simp [resourceNeeds, Tmem.Pair.allocResultNeeds, hg0])
        cases x with
        | async => exact hfill.elim
        | thread store =>
          obtain ⟨D, hsw, hl0, hDs, hDc, j', site, group, n', k', bytes, hj', hlead, hgi, hk1, hk2,
            hst⟩ := hfill
          have hkk : k' = k := hk2.2.symm.trans hgk.2
          subst hkk
          exact ⟨.thread store, hxp, D, Step.sameWarp_trans hsw hs, hl0, hDs, hDc.trans hcta, j',
            site, group, n', k', bytes, hj', hlead, (hgh.trans hg.symm).trans hgi, hk1, hhk, hst⟩
    | _ => simp [Tmem.Pair.allocResultNeeds] at hn
  simp only [List.mem_append, List.mem_cons] at hn
  rcases hn with hn | rfl | hn
  · obtain ⟨h', hh', rfl⟩ := List.mem_map.mp hn
    obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hh'
    have hlt := Sched.warpLane_lt hs.1.2.1 (List.mem_range.mp hl')
    have hsw := sameWarp_of_mem_warpLanes hh' hlt hs.1.2.1
    obtain ⟨i, hi⟩ := hall _ hlt (Step.sameWarp_trans hs (sameWarp_symm hsw))
    obtain ⟨ev, hev, -⟩ := hi.1
    exact ⟨.thread (warpLane L h l', i), ⟨_, hev⟩, i, rfl, hhk.2 ▸ hi⟩
  · exact ⟨cta, r, hrm, l1, hl1⟩
  · have hm : Tmem.Pair.MustWait X (h, l) := ⟨pc, .one, dst, act, hgh, by cases act <;> simp⟩
    simp only [needsIf, hm, ↓reduceIte] at hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact hcovh
    · cases act with
      | alloc nc =>
        simp only [List.append_eq, List.nil_append, List.mem_flatMap, List.mem_range] at hn
        obtain ⟨j', hj', hn⟩ := hn
        split_ifs at hn
        · obtain ⟨l', -, rfl⟩ := List.mem_map.mp hn
          obtain ⟨d, hd⟩ : ∃ d, (X.tmemHistory ((h, l).1 / L.block))[j']? = some d :=
            ⟨_, List.getElem?_eq_getElem hj'⟩
          have hdv := ((hv.1 _).1 d (List.mem_of_getElem? hd)).2.2
          exact ⟨.thread (d.own.event L l'), ⟨_, hdv.2.2.1 l'⟩, d, hd, rfl⟩
        · cases hn
      | _ => simp at hn

/-- **A synchronizing event of a lane of the warp of a released lane, which that lane has also
made, ends the first lane's trace ready**: a register request of the same ordinal and operands
(`SetMaxNReg.ready_of_sameRequest`), a warp-collective `tcgen05` event of the same ordinal
(every lane has made it; for an allocator operation, `ready_res_lane`), a `bar.sync` of the same
barrier and ordinal on it (`ready_bar_lane`). -/
theorem released_of_sync (hX : Consistent L kernel asms mem0 X) {g h j : Nat} {x : SyncEv}
    (hs : SameWarp L g h) (hrel : Step.Released L X g) (hxg : SyncAt X g j x)
    (hxh : SyncAt X h ((X.tr h).length - 1) x) (hpub : AllocStored L X g) :
    Step.Released L X h := by
  refine ⟨fun pc k hq hk => ?_⟩
  cases x with
  | reg pcr inc n o =>
    obtain ⟨ig, hqg, hog⟩ := hxg
    obtain ⟨ih, hqh, hoh⟩ := hxh
    exact SetMaxNReg.ready_of_sameRequest hqg ⟨hs, hog.trans hoh.symm, pcr, inc, n, ig, ih,
      hqg, hqh⟩ (ready_at hX hrel hqg rfl)
  | tc res k =>
    obtain ⟨hKg, hng, hrg⟩ := hxg
    obtain ⟨hKh, hnh, hrh⟩ := hxh
    obtain ⟨⟨qg, hqg, hcg⟩, hog⟩ := id hKg
    obtain ⟨pcg, kdg, rfl⟩ := isTcColl_tc hcg
    have hready := ready_at hX hrel hqg
      (by cases kdg <;> simp_all [isTcColl, Kind.resume, TcKind.resume])
    obtain ⟨⟨qh, hqh, hch⟩, -⟩ := id hKh
    obtain ⟨pch, kdh, rfl⟩ := isTcColl_tc hch
    cases kdh with
    | resource grh dsth acth =>
      have hres : res = true := hrh.mp ⟨_, _, _, _, hqh⟩
      obtain ⟨pg', grg, dstg, actg, hqg'⟩ := hrg.mpr hres
      have hgo : grg = .one := by
        cases grg
        · rfl
        · exact absurd hqg' (hng _ _ _)
      subst hgo
      exact ready_res_lane hX hs hready hqg' hKg hKh fun n hn hg0 => hpub (hn ▸ hqg') hg0
    | _ =>
      first
        | simp [isTcColl] at hch; done
        | refine Sched.tc_ready_of_done hs.1.2.1 hqh (fun _ _ _ he => by cases he) hKh ?_
          intro h' _ hw'
          have hw : SameWarp L h' g := sameWarp_symm (Step.sameWarp_trans hs hw')
          obtain ⟨y, -, i, rfl, hi⟩ := hready _ (tcNeed_mem hqg hcg (mem_warpLanes_of_sameWarp hw))
          exact ⟨i, hog ▸ hi⟩
  | bar b o =>
    obtain ⟨cg, pcg, hbg, hog⟩ := hxg
    obtain ⟨ch, pch, hbh, hoh⟩ := hxh
    exact ready_bar_lane hX hs (ready_at hX hrel hbg rfl) hbg hog hbh hoh

/-- **A lane at the warp collective of a released lane is released**, both having made equally
many warp collectives. -/
theorem lane_released (hX : Consistent L kernel asms mem0 X) (hw : WarpCollFacts T Q L X)
    {g h : Nat} (hpub : AllocStored L X g) (hg : g < L.threads) (hs : SameWarp L g h) {d dh : TSt}
    (hσ : St Q L X g (X.tr g).length = some (some d)) (hk : nextKind d = .warp)
    (hσh : St Q L X h (X.tr h).length = some (some dh)) (hkh : nextKind dh = .warp)
    (hn : (X.tr h).countP Sched.isWarpColl = (X.tr g).countP Sched.isWarpColl)
    (hrel : Step.Released L X g) : Step.Released L X h := by
  obtain ⟨R, hR⟩ := hw.last
  have hlg := hR hg hσ hk
  have hlh := hR hs.1.2.1 hσh hkh
  rw [hn, ← warpKey_eq hs] at hlh
  revert hlg hlh
  cases R (warpKey L g) ((X.tr g).countP Sched.isWarpColl) with
  | none => exact fun _ hlh => released_of_free hlh
  | some x =>
    rintro ⟨⟨j, -, hxg⟩, -⟩ ⟨-, hfree | hxh⟩
    · exact released_of_free hfree
    · exact released_of_sync hX hs hrel hxg hxh hpub

end

end PTX.Kernels.InklingRelDecode.Proof.Progress
