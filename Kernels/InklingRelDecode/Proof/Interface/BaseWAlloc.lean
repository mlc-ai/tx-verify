-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.IpTmAlloc
public import Kernels.InklingRelDecode.Proof.Interface.BaseWEarly

@[expose] public section

/-!
# The allocation's store writes the zero word, under the tracking up to the base-word stops

`allocWordZero_w` proves `AllocWordZero Q L X` (`ScBase.lean`) from `WeakTracked` in place of
`ThreadFacts`. The argument of `Tmem1.allocWordZero` classifies every resource event of every
thread (`Tmem1Ops`), which needs every thread followed at every event. Here only the allocation's
own record and the first record of its CTA's history are classified:

* the allocation is a thread's first event: no step of a machine goes into the allocation's state
  (`next_ne_alloc`), so the state is the initial one, of a thread of warp 0 (`alloc_first`);
* the allocation of the CTA's thread 0 is complete, since its thread went on, and its record is
  a `cta_group::1` record of the CTA's history (`alloc_record`);
* no record precedes it in the history (`alloc_head`). The lane-0 event of an earlier record is a
  resource event of a thread of the CTA. If that thread made a barrier-0 arrival before it, the
  allocation is before the event through the early `bar.sync 0` (`bar0_chain'`), and
  `ObjectCoherent.not_precedes` excludes the order. If not, the thread is followed at the event
  (`EarlyTT`), the event is an allocation (`res_early_alloc`), so it is the first event of the
  CTA's thread 0, which is the allocation itself, and the order is again excluded;
* the history's first record allocates at column 0 of the empty allocator, and the allocator's
  result is the store's word (`Consistent.tmemPairResult`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode Tmem.Pair
open PTX.Kernels.InklingRelDecode.Proof.Bar PTX.Kernels.InklingRelDecode.Proof.BarOrd
open PTX.Kernels.InklingRelDecode.Proof.IpTm

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **No step of a machine goes into the allocation's state.** -/
theorem next_ne_alloc {g : Nat} {s : TSt} {e : Event} {tm : Value} :
    (threadCode L g Q).next s e ≠ some (some (.d (.dstart ⟨.alloc, tm⟩))) := by
  intro hn
  cases s with
  | w s =>
    obtain ⟨a, -, h⟩ := map_map_eq_some_some (show (WComp.next L g s e).map
      (Option.map TSt.w) = some (some (.d (.dstart ⟨.alloc, tm⟩))) from hn)
    cases h
  | d s =>
    obtain ⟨a, ha, h⟩ := map_map_eq_some_some (show (DComp.next L g Q s e).map
      (Option.map TSt.d) = some (some (.d (.dstart ⟨.alloc, tm⟩))) from hn)
    have h' : a = .dstart ⟨.alloc, tm⟩ := TSt.d.inj h
    subst h'
    cases s with
    | dstart d =>
      obtain ⟨site, tm0⟩ := d
      cases site
      all_goals
        simp only [DComp.next, DComp.dstartNext, DStart.next, Option.map_some,
          Option.some.injEq] at ha
        repeat' split at ha
        all_goals simp at ha
    | pro d => exact absurd rfl (pro_ne ha ⟨.alloc, tm⟩)
    | sm d => exact absurd rfl (sm_ne ha ⟨.alloc, tm⟩)
    | epi d =>
      exact absurd rfl (map_ne (f := DComp.St.epi) (fun _ _ => by simp) ha ⟨.alloc, tm⟩)

/-- **The allocation's state is a thread's first state**, of a thread of warp 0. -/
theorem alloc_first {g i : Nat} {tm : Value} (hi : i ≤ (X.tr g).length)
    (hσ : St Q L X g i = some (some (.d (.dstart ⟨.alloc, tm⟩)))) :
    i = 0 ∧ g % L.block < 32 := by
  cases i with
  | zero =>
    refine ⟨rfl, ?_⟩
    by_contra h32
    have hs : Frame.stateAt (code L Q) X g 0 = some (some (.d (.dstart ⟨.alloc, tm⟩))) := hσ
    rw [Frame.stateAt_zero] at hs
    have h2 := Option.some.inj (Option.some.inj hs)
    change (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
      else .w (WComp.code L g Q).init) = _ at h2
    split_ifs at h2
    change TSt.d (.dstart (DStart.D.start L g)) = _ at h2
    simp [DStart.D.start, h32] at h2
  | succ i0 =>
    exfalso
    obtain ⟨e0, he0⟩ : ∃ e0, (X.tr g)[i0]? = some e0 :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hσ' : Frame.stateAt (code L Q) X g (i0 + 1) =
        some (some (.d (.dstart ⟨.alloc, tm⟩))) := hσ
    rw [Frame.stateAt_succ he0] at hσ'
    cases hk0 : Frame.stateAt (code L Q) X g i0 with
    | none => rw [hk0] at hσ'; simp at hσ'
    | some o =>
      cases o with
      | none => rw [hk0] at hσ'; simp [Flow.Code.toMachine] at hσ'
      | some s0 =>
        rw [hk0] at hσ'
        simp only [Option.bind_some] at hσ'
        exact next_ne_alloc hσ'

/-- **A resource event before its thread's first barrier-0 arrival is fired from the
allocation's state**, at a followed state. -/
theorem res_early_alloc (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) {g k pc : Nat} {grp : CtaGroup}
    {dst : Option Loc} {act : Tmem.Request} {s : TSt} (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .tc (.resource grp dst act)⟩)
    (hσ : St Q L X g k = some (some s))
    (hc : ((X.tr g).take k).countP (Execution.isBarId 0) = 0) :
    ∃ tm, s = .d (.dstart ⟨.alloc, tm⟩) := by
  have hk : k ≤ (X.tr g).length := ev_le he
  have hlb := (ordinal_inv hX hS k s hk hσ).1
  rw [hc] at hlb
  obtain ⟨t, ins, o, -, -, hcode, hfire⟩ := Frame.fired_site hS hX he hσ
  have hop : tmemOp ins.op = true := fires_resource_op hfire rfl
  have hpc : TSt.pc s ∈ resPcs := OpPcsFast.mem kernel_res_pcs hcode hop
  cases s with
  | w s => exact absurd hpc (worker_notRes s)
  | d s =>
    cases s with
    | dstart d =>
      obtain ⟨site, tm⟩ := d
      have hs : site ∈ ([.alloc, .allocWr, .relinq] : List DStart.Site) :=
        dstart_res_pc site hpc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl
      · exact ⟨tm, rfl⟩
      · exfalso
        obtain ⟨u, hF⟩ := fired_cont_at hX hS hT hg he hσ (by simp [ExitState])
        have hshape := DStart.shape_of_pre hpre (fired_dstart hF)
        simp only [DStart.Shape] at hshape
        obtain ⟨col, -, hshape⟩ := hshape
        simp only [Event.mk.injEq] at hshape
        cases hshape.2
      · exfalso
        simp [tLb, dLb] at hlb
    | pro d => exact absurd hpc (fun h => by simpa using pro_res_pc d.site h)
    | sm d => exact absurd hpc (fun h => by simpa using sm_res_pc d.site h)
    | epi d =>
      exfalso
      simp [tLb_epi] at hlb

/-- **The allocation of a CTA's thread 0 is a record of the CTA's history**, with the
allocation as its lane 0: the operation is `cta_group::1` and complete, since its thread went
on. -/
theorem alloc_record (hX : Consistent L kernel asms mem0 X) {cta k pc : Nat}
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
theorem alloc_head (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) (hW : WeakTracked Q L X) {cta pc : Nat}
    {dst : Option Loc} {act : Tmem.Request} {r : Requests} (hr : r ∈ X.tmemHistory cta)
    (hg : cta * L.block < L.threads) (hwi : r.own.event L 0 = (cta * L.block, 0))
    (he : X.get (cta * L.block, 0) = some ⟨pc, .tc (.resource .one dst act)⟩) :
    ∃ rest, X.tmemHistory cta = r :: rest := by
  have hbk : L.block = 256 := hpre.block
  have hb : 0 < L.block := by omega
  have hE : EarlyTT Q L X := earlyTT_of_weak hX hS hW
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
    by_cases hc : ((X.tr h).take i).countP (Execution.isBarId 0) = 0
    · -- the thread is followed at the event: the event is the allocation itself
      obtain ⟨s, hσ⟩ := event_state_at hS hX hget (by intro pc' f h; cases h)
        (hE h i h3 (by omega))
      obtain ⟨tm, rfl⟩ := res_early_alloc hpre hX hS hT h3 hget hσ hc
      obtain ⟨rfl, hl32⟩ := alloc_first hil.le hσ
      have hw0 : x.own.warp = 0 := by omega
      rw [hw0] at hh
      simp only [Nat.zero_mul, Nat.add_zero] at hh
      subst hh
      exact hX.object.not_precedes hP .refl
    · -- the thread's barrier-0 arrival of ordinal 0 is before the event
      obtain ⟨jf, pcf, hjf, hf, hord⟩ := arrival_before' hX hS hE (h := h) (k := i) (r := 0)
        (by omega) (by omega)
      have hsame : SameCta L (cta * L.block) h := ⟨hg, h3, by rw [hcta0, h1, hown]⟩
      have hbl : 0 < (X.tr (cta * L.block)).length := (List.getElem?_eq_some_iff.mp he).1
      have hbn : ∀ ev, (X.tr (cta * L.block))[0]? = some ev →
          ¬ Execution.isBarId 0 ev = true := by
        intro ev hev
        have hev' : X.get (cta * L.block, 0) = some ev := hev
        rw [he] at hev'
        cases hev'
        simp [Execution.isBarId]
      have hbc : baseCausality L X (cta * L.block, 0) (h, i) :=
        bar0_chain' hpre hX hS hE hsame hf (by omega) (by simp) hbl hbn hjf hil
      have e1 : stageCausality L X (.thread (cta * L.block, 0), true)
          (.thread (h, i), false) :=
        .inr (.inl ⟨rfl, rfl, _, _, rfl, rfl, hbc⟩)
      have e2 : stageCausality L X (.thread (h, i), false) (.thread (h, i), true) :=
        .inl (.inl ⟨rfl, rfl, rfl, ⟨_, hget⟩⟩)
      exact hX.object.not_precedes hP (.tail (.single e1) e2)

/-- **`AllocWordZero` under the tracking up to the base-word stops**: the store of the address
that the allocation of a CTA's thread 0 returns writes the zero word. -/
theorem allocWordZero_w (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hS : ∀ g < L.threads, (threadCode L g Q).Sound)
    (hT : ∀ g < L.threads, (threadCode L g Q).TmplOk) (hW : WeakTracked Q L X) :
    AllocWordZero Q L X := by
  intro g k pc a bs tm hget hσ
  have hg : g < L.threads := Frame.lt_of_get hX hget
  have hklt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp hget).1
  have hbk : L.block = 256 := hpre.block
  cases k with
  | zero =>
    exfalso
    have hs : Frame.stateAt (code L Q) X g 0 = some (some (.d (.dstart ⟨.allocWr, tm⟩))) := hσ
    rw [Frame.stateAt_zero] at hs
    have h2 := Option.some.inj (Option.some.inj hs)
    change (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
      else .w (WComp.code L g Q).init) = _ at h2
    split_ifs at h2
    · change TSt.d (.dstart (DStart.D.start L g)) = _ at h2
      unfold DStart.D.start at h2
      split_ifs at h2 <;> simp at h2
  | succ k0 =>
    obtain ⟨e0, he0⟩ : ∃ e0, (X.tr g)[k0]? = some e0 :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hσ' : Frame.stateAt (code L Q) X g (k0 + 1) =
        some (some (.d (.dstart ⟨.allocWr, tm⟩))) := hσ
    rw [Frame.stateAt_succ he0] at hσ'
    cases hk0 : Frame.stateAt (code L Q) X g k0 with
    | none => rw [hk0] at hσ'; simp at hσ'
    | some o =>
      cases o with
      | none => rw [hk0] at hσ'; simp [Flow.Code.toMachine] at hσ'
      | some s0 =>
        rw [hk0] at hσ'
        simp only [Option.bind_some] at hσ'
        have hn : (threadCode L g Q).next s0 e0 =
            some (some (.d (.dstart ⟨.allocWr, tm⟩))) := hσ'
        obtain ⟨⟨tm0, rfl⟩, hlane⟩ := Tmem1.pred_allocWr hn
        have hk0' : St Q L X g k0 = some (some (.d (.dstart ⟨.alloc, tm0⟩))) := hk0
        obtain ⟨rfl, hl⟩ := alloc_first (by omega) hk0'
        have hget0 : X.get (g, 0) = some e0 := he0
        obtain ⟨u, hF⟩ := fired_cont_at hX hS hT hg hget0 hk0' (by simp [ExitState])
        have hshape := DStart.shape_of_pre hpre (fired_dstart hF)
        simp only [DStart.Shape] at hshape
        subst hshape
        have hlane' : g % L.block % 32 = 0 := hlane
        have hg0 : g % L.block = 0 := by omega
        obtain ⟨cta, hcta⟩ : ∃ cta, g = cta * L.block := ⟨g / L.block, by
          have := Nat.div_add_mod g L.block
          rw [Nat.mul_comm] at this
          omega⟩
        subst hcta
        have hal : X.get (cta * L.block, 0) = some ⟨DStart.evPc DStart.Site.alloc,
            .tc (.resource .one (some ⟨.shared, cta * L.block / L.block, L.sharedBase⟩)
              (.alloc 512))⟩ := hget0
        obtain ⟨r, hr, hwi⟩ := alloc_record hX (by omega) hal (by omega)
        obtain ⟨rest, hh⟩ := alloc_head hpre hX hS hT hW hr hg hwi hal
        obtain ⟨base, hwa⟩ : ∃ base, r.action = .alloc 512 base := by
          obtain ⟨-, hreq, hv⟩ := (hX.tmemPair.1 cta).1 r hr
          have hev := hv.2.2.1 0
          rw [hwi, hal] at hev
          simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq,
            TcKind.resource.injEq] at hev
          exact Tmem.Action.request_eq_alloc (hreq.trans hev.2.2.2.symm)
        have hbase : base = 0 := by
          have hrun := (hX.tmemPair.1 cta).2.2
          rw [hh] at hrun
          by_contra hc
          apply hrun
          simp [runRequests, hwa, perform_alloc, hc]
        subst hbase
        exact hX.tmemPairResult (cta * L.block, 0) _ .one _ 512 hal cta r 0 hr hwi hwa pc a bs
          hget

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
