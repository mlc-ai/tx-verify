-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Staged.Bar0
public import Lemmas.Tmem.TmemPairOrder
public import Lemmas.Tmem.TmemPairHistory
public import Lemmas.Tmem.TmemRun
public import Lemmas.Tmem.TmemPairRecord

@[expose] public section

/-! # The allocation's store writes column 0, and it is the only early store

`early_write`: a store of a thread with at most one barrier-0 event before it is the allocation's
store of a CTA's thread 0, its second event, and it writes the 32-bit word 0 at the CTA's shared
base. From the first stage of the following and barrier 0's first two instances only (no
`BaseRead`):

* by the startup's shape, an early store is fired from the `allocWr` state, which only the
  `alloc` state of a thread of warp 0's lane 0 steps into, and that is the thread's first state
  (`allocWr_at`);
* the allocation is lane 0 of a `cta_group::1` record of the CTA's Tensor Memory history
  (`alloc_record`);
* no record precedes it (`alloc_head`): the lane-0 event of an earlier record is a resource event
  of a thread of the CTA; before that thread's first barrier-0 event it is that thread's
  allocation (the startup's shape), so the allocation itself; after it, the allocation is before
  it by barrier 0's first instance (`bar0_before`); either way `ObjectCoherent.not_precedes`
  excludes the order;
* the history's first record allocates from the empty allocator, so at column 0
  (`perform_alloc`), and the stored word is the allocator's column (`Consistent.tmemPairResult`).
 -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Proof PTX.Flow Tmem.Pair
open PTX.Kernels.InklingRelDecode

noncomputable section

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- A startup state that a startup step enters is that step's successor. -/
theorem enter_eq {s' t : Startup.D}
    (h : Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) s' = .inl t) : s' = t := by
  unfold Code.enter at h
  split at h
  · cases h
  · exact Sum.inl.inj h

/-- The thread machine's step into a startup state is a startup step. -/
theorem pred_start {σ : (thread Q L g).D} {e : Event} {t : Startup.D} {n' : Cls → Nat}
    (h : (thread Q L g).next σ e = some (some (.inl t, n'))) :
    ∃ s n, σ = (.inl s, n) ∧ Startup.succ L g s e = some (some t) := by
  obtain ⟨x, n⟩ := σ
  rcases x with s | y
  · rw [next_start] at h
    rcases hs : Startup.succ L g s e with _ | _ | s'
    · rw [hs] at h; cases h
    · rw [hs] at h; cases h
    · rw [hs] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨s, n, rfl, by rw [← enter_eq h.1]; exact hs⟩
  · obtain ⟨⟨y', hy⟩, -⟩ := next_role h
    simp at hy

/-- The startup's state before position `k + 1`, when the state at `k + 1` is a startup state. -/
theorem prev_start {k : Nat} {t : Startup.D}
    {n' : Cls → Nat} (hk : k < (X.tr g).length)
    (h : Frame.stateAt (thread Q L) X g (k + 1) = some (some (.inl t, n'))) :
    ∃ s n e, Frame.stateAt (thread Q L) X g k = some (some (.inl s, n)) ∧
      X.get (g, k) = some e ∧ Startup.succ L g s e = some (some t) := by
  obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hk⟩
  rw [Frame.stateAt_succ he] at h
  cases hk0 : Frame.stateAt (thread Q L) X g k with
  | none => rw [hk0] at h; cases h
  | some o =>
    cases o with
    | none => rw [hk0] at h; cases h
    | some σ =>
      rw [hk0] at h
      obtain ⟨s, n, rfl, hs⟩ := pred_start (σ := σ) h
      exact ⟨s, n, e, rfl, he, hs⟩

/-- **The allocation's state is a thread's first state**, of warp 0. -/
theorem alloc_at {k : Nat} {s : Startup.D}
    {n : Cls → Nat} (hk : k ≤ (X.tr g).length) (hs : s.site = .alloc)
    (h : Frame.stateAt (thread Q L) X g k = some (some (.inl s, n))) :
    k = 0 ∧ g % L.block < 32 := by
  cases k with
  | zero =>
    refine ⟨rfl, ?_⟩
    rw [Frame.stateAt_zero] at h
    have h2 := congrArg Prod.fst (Option.some.inj (Option.some.inj h))
    change Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) (Startup.init L g) = _ at h2
    rw [enter_inl enterOf_init] at h2
    have h3 := Sum.inl.inj h2
    by_contra hw
    unfold Startup.init at h3
    simp only [hw, ↓reduceIte] at h3
    rw [← h3] at hs
    cases hs
  | succ k0 =>
    exfalso
    obtain ⟨s0, n0, e0, -, -, hsu⟩ := prev_start (by omega) h
    obtain ⟨site, tm, x, bw⟩ := s0
    cases site <;> simp only [Startup.succ] at hsu <;>
      (repeat' split at hsu) <;> simp only [Option.some.injEq, reduceCtorEq] at hsu <;>
      (try subst hsu) <;> simp_all

/-- **The allocation's store is the second event of a thread of warp 0's lane 0.** -/
theorem allocWr_at {k : Nat} {s : Startup.D}
    {n : Cls → Nat} (hk : k ≤ (X.tr g).length) (hs : s.site = .allocWr)
    (h : Frame.stateAt (thread Q L) X g k = some (some (.inl s, n))) :
    k = 1 ∧ g % L.block = 0 ∧
      ∃ s0 n0, Frame.stateAt (thread Q L) X g 0 = some (some (.inl s0, n0)) ∧
        s0.site = .alloc := by
  cases k with
  | zero =>
    exfalso
    rw [Frame.stateAt_zero] at h
    have h2 := congrArg Prod.fst (Option.some.inj (Option.some.inj h))
    change Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) (Startup.init L g) = _ at h2
    rw [enter_inl enterOf_init] at h2
    have h3 := Sum.inl.inj h2
    unfold Startup.init at h3
    split at h3 <;> (rw [← h3] at hs; cases hs)
  | succ k0 =>
    obtain ⟨s0, n0, e0, h0, -, hsu⟩ := prev_start (by omega) h
    obtain ⟨site, tm, x, bw⟩ := s0
    have hal : site = .alloc ∧ laneOf L g = 0 := by
      cases site <;> simp only [Startup.succ] at hsu <;>
        (repeat' split at hsu) <;> simp only [Option.some.injEq, reduceCtorEq] at hsu <;>
        (try subst hsu) <;> simp_all
    obtain ⟨rfl, hl⟩ := hal
    obtain ⟨rfl, hw⟩ := alloc_at (by omega) rfl h0
    refine ⟨rfl, ?_, _, _, h0, rfl⟩
    unfold laneOf at hl
    omega

/-- **The allocation of a CTA's thread 0 is a record of the CTA's history**, with the
allocation as its lane 0 (the first tree's `alloc_record`). -/
theorem alloc_record (hX : Consistent L kernel Assumptions.all m X) {cta k pc : Nat}
    {dst : Option Loc} {act : Tmem.Request} (hb : 0 < L.block)
    (he : X.get (cta * L.block, k) = some ⟨pc, .tc (.resource .one dst act)⟩)
    (hk : k + 1 < (X.tr (cta * L.block)).length) :
    ∃ r ∈ X.tmemHistory cta, r.own.event L 0 = (cta * L.block, k) := by
  obtain ⟨ws, hws, q, hq, lane, hl⟩ :=
    hX.tmemPairBlocking.covered ⟨pc, _, _, _, he, by cases act <;> simp⟩ hk
  rcases hws with ⟨cta', x, hx, -, rfl⟩ | ⟨p, hp, rfl⟩
  · rw [List.mem_singleton.mp hq] at hl
    obtain ⟨hval, hown, -⟩ := hX.tmemPair.1 cta'
    have hv := (hval x hx).2.2
    obtain ⟨h1, -, -⟩ := WarpRequest.event_props hv lane
    rw [hl] at h1
    have hcx : x.own.cta = cta := by
      rw [← h1]
      exact Nat.mul_div_cancel cta hb
    have hcc : cta' = cta := (hown x hx).symm.trans hcx
    subst hcc
    simp only [WarpRequest.event, Prod.mk.injEq] at hl
    obtain ⟨hl1, hl2⟩ := hl
    rw [hcx] at hl1
    have hlane : lane = 0 := by
      ext
      simp only [Fin.val_zero]
      omega
    subst hlane
    refine ⟨x, hx, ?_⟩
    simp only [WarpRequest.event, Fin.val_zero, Prod.mk.injEq]
    exact ⟨by rw [hcx]; omega, hl2⟩
  · exfalso
    obtain ⟨⟨-, hv1, hv2, -⟩, -⟩ := hX.tmemPair.2.1 p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · have h := hv1.2.2.1 lane
      rw [hl, he] at h
      simp at h
    · have h := hv2.2.2.1 lane
      rw [hl, he] at h
      simp at h

/-- **No record precedes the allocation of a CTA's thread 0 in the CTA's history.** -/
theorem alloc_head (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {cta pc : Nat} {dst : Option Loc} {act : Tmem.Request} {r : Requests}
    (hr : r ∈ X.tmemHistory cta) (hg : cta * L.block < L.threads)
    (hwi : r.own.event L 0 = (cta * L.block, 0))
    (he : X.get (cta * L.block, 0) = some ⟨pc, .tc (.resource .one dst act)⟩) :
    ∃ rest, X.tmemHistory cta = r :: rest := by
  have hbk : L.block = 256 := hp.block
  have hb : 0 < L.block := by omega
  obtain ⟨l, hl, hlr⟩ := List.getElem_of_mem hr
  rcases Nat.eq_zero_or_pos l with rfl | hpos
  · cases hH : X.tmemHistory cta with
    | nil => simp [hH] at hl
    | cons x rest =>
      refine ⟨rest, ?_⟩
      simp only [hH, List.getElem_cons_zero] at hlr
      rw [hlr]
  · exfalso
    obtain ⟨x, hx0⟩ : ∃ x, (X.tmemHistory cta)[0]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hx : x ∈ X.tmemHistory cta := List.mem_of_getElem? hx0
    obtain ⟨-, -, hv⟩ := (hX.tmemPair.1 cta).1 x hx
    have hown : x.own.cta = cta := (hX.tmemPair.1 cta).2.1 x hx
    have hget := hv.2.2.1 0
    obtain ⟨h1, h2, h3⟩ := WarpRequest.event_props hv 0
    have hP : Precedes L X cta (x.own.event L 0) (cta * L.block, 0) :=
      ⟨0, l, x, r, hx0, by rw [List.getElem?_eq_getElem hl, hlr], hpos, ⟨0, rfl⟩, ⟨0, hwi⟩⟩
    have hev : x.own.event L 0 = (cta * L.block + x.own.warp * 32, x.own.indices 0) := by
      simp [WarpRequest.event, hown]
    rw [hev] at hget h1 h2 h3 hP
    simp only at h1 h2 h3
    generalize hh : cta * L.block + x.own.warp * 32 = h at hget h1 h2 h3 hP
    generalize hi : x.own.indices 0 = i at hget h1 h2 h3 hP
    have hil : i < (X.tr h).length := (List.getElem?_eq_some_iff.mp hget).1
    have hcta0 : cta * L.block / L.block = cta := Nat.mul_div_cancel cta hb
    by_cases hc : c0 X h i = 0
    · -- before its thread's first barrier: the allocation of a thread of warp 0, at position 0
      obtain ⟨s, n, hσ, hs, -, hE⟩ := early_at (Q := Q) hp hX hget (by simp) (by omega)
      have hsite : s.site = .alloc := by
        obtain ⟨site, tm, xx, bw⟩ := s
        simp only at hs ⊢
        rcases hs with rfl | rfl | rfl | rfl | rfl <;> simp only [Startup.Ev] at hE
        · rfl
        · obtain ⟨col, -, hE⟩ := hE; simp at hE
        · simp at hE
        · obtain ⟨_, _, hE, _⟩ := hE; simp at hE
        · simp at hE
      obtain ⟨rfl, hl32⟩ := alloc_at hil.le hsite hσ
      have hw0 : x.own.warp = 0 := by omega
      rw [hw0] at hh
      simp only [Nat.zero_mul, Nat.add_zero] at hh
      subst hh
      exact hX.object.not_precedes hP .refl
    · -- after it: the allocation is before the event by barrier 0's first instance
      have hsame : SameCta L (cta * L.block) h := ⟨hg, h3, by rw [hcta0, h1, hown]⟩
      have hc1 : c0 X (cta * L.block) (0 + 1) = 0 := by
        rw [c0_succ (show (X.tr (cta * L.block))[0]? = _ from he)]
        simp [c0, Execution.isBarId]
      have hbc : baseCausality L X (cta * L.block, 0) (h, i) :=
        bar0_before (Q := Q) hp hX hsame hil (by omega) (by omega)
      have e1 : stageCausality L X (.thread (cta * L.block, 0), true)
          (.thread (h, i), false) :=
        .inr (.inl ⟨rfl, rfl, _, _, rfl, rfl, hbc⟩)
      have e2 : stageCausality L X (.thread (h, i), false) (.thread (h, i), true) :=
        .inl (.inl ⟨rfl, rfl, rfl, ⟨_, hget⟩⟩)
      exact hX.object.not_precedes hP (.tail (.single e1) e2)

/-- **An early store is the allocation's store of a CTA's thread 0, and it writes the word 0 at
the CTA's shared base.** -/
theorem early_write (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {k pc : Nat}
    {a : Acc} {bs : List Byte} (hget : X.get (g, k) = some ⟨pc, .wr a bs⟩) (hc : c0 X g k ≤ 1) :
    k = 1 ∧ g % L.block = 0 ∧
      a = { loc := ⟨.shared, g / L.block, L.sharedBase⟩, size := 4 } ∧
      bs = (b32 0).toBytes := by
  have hg : g < L.threads := Frame.lt_of_get hX hget
  have hbk : L.block = 256 := hp.block
  have hklt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp hget).1
  obtain ⟨s, n, hσ, hs, -, hE⟩ := early_at (Q := Q) hp hX hget (by simp) hc
  have hsite : s.site = .allocWr := by
    obtain ⟨site, tm, xx, bw⟩ := s
    simp only at hs ⊢
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> simp only [Startup.Ev] at hE
    · simp at hE
    · rfl
    · simp at hE
    · obtain ⟨_, _, hE, _⟩ := hE; simp at hE
    · simp at hE
  have hE' := hE
  obtain ⟨site, tm, xx, bw⟩ := s
  simp only at hsite
  subst hsite
  simp only [Startup.Ev] at hE'
  obtain ⟨col, -, hE'⟩ := hE'
  simp only [Event.mk.injEq, Kind.wr.injEq] at hE'
  obtain ⟨-, rfl, rfl⟩ := hE'
  obtain ⟨rfl, hg0, s0, n0, h0, hs0⟩ := allocWr_at hklt.le rfl hσ
  refine ⟨rfl, hg0, rfl, ?_⟩
  -- the allocation event at position 0
  have hu0 : ∀ f, ∀ e0, X.get (g, 0) = some e0 → e0.kind ≠ .ub f := by
    intro f e0 h0' hk
    obtain ⟨pc0, kd⟩ := e0
    simp only at hk
    subst hk
    have := ub_last hX h0' hget
    omega
  obtain ⟨e0, he0⟩ : ∃ e0, X.get (g, 0) = some e0 :=
    ⟨_, List.getElem?_eq_getElem (show 0 < (X.tr g).length by omega)⟩
  have hE0 := start_ev hp hX he0 h0 (fun f => hu0 f e0 he0)
  obtain ⟨site0, tm0, x0, bw⟩ := s0
  simp only at hs0
  subst hs0
  simp only [Startup.Ev] at hE0
  subst hE0
  obtain ⟨cta, hcta⟩ : ∃ cta, g = cta * L.block := ⟨g / L.block, by
    have := Nat.div_add_mod g L.block
    rw [Nat.mul_comm] at this
    omega⟩
  subst hcta
  have hcd : cta * L.block / L.block = cta := Nat.mul_div_cancel cta (by omega)
  obtain ⟨r, hr, hwi⟩ := alloc_record hX (by omega) he0 (by omega)
  obtain ⟨rest, hh⟩ := alloc_head (Q := Q) hp hX hr hg hwi he0
  obtain ⟨base, hwa⟩ : ∃ base, r.action = .alloc 512 base := by
    obtain ⟨-, hreq, hv⟩ := (hX.tmemPair.1 cta).1 r hr
    have hev := hv.2.2.1 0
    rw [hwi, he0] at hev
    simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq,
      TcKind.resource.injEq] at hev
    obtain ⟨-, -, -, haction⟩ := hev
    exact Tmem.Action.request_eq_alloc (hreq.trans haction.symm)
  have hbase : base = 0 := by
    have hrun := (hX.tmemPair.1 cta).2.2
    rw [hh] at hrun
    by_contra hc'
    apply hrun
    simp [runRequests, hwa, perform_alloc, hc']
  subst hbase
  exact hX.tmemPairResult (cta * L.block, 0) _ .one _ 512 he0 cta r 0 hr hwi hwa _ _ _ hget

end
end PTX.Kernels.InklingRelDecode.Proof
