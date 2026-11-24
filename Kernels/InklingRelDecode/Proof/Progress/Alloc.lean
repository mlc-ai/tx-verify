-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Progress.NextIssue
public import Lemmas.Flow.OpPcsFast
public import Lemmas.Tmem.Alloc512
public import Kernels.InklingRelDecode.Proof.Interface.ShapeTrace
public import Kernels.InklingRelDecode.Proof.Interface.FootClass
public import Lemmas.Tmem.AllocResult
public import Lemmas.Tmem.TmemResourceReady

@[expose] public section

/-!
# The Tensor Memory allocation in the progress layer

Two of the facts `Remaining` needs about the allocation are proved from the program text and the
thread machines.

* **`alloc_base`**: every recorded allocation returns column 0. Every `tcgen05.alloc` of the
  program requests the immediate 512 columns (`kernel_allocN`, `decide +kernel`), so a recorded
  allocation is a 512-column request, which the allocator of a CTA whose history replays without a
  fault (`tmemNoFault_of_safe`: a safe execution) places at column 0
  (`Consistent.alloc512_base`).
* **`alloc_next`**: a thread whose last event is an allocation request is at the address store
  or is not lane 0 of its warp. The only `tcgen05.alloc` instruction is the common start's
  (`alloc_pcs`); its state `DStart.Site.alloc` has the successor `allocWr` (the address store) for
  lane 0 and `bar0` for the other lanes (`DStart.next`).
* **`alloc_result_event`**: on lane 0, the allocation names the word at the shared base, and the
  event after it, if any, is the store of that word at the same site.
* **`publish_steps`**: a lane of the allocating warp whose allocation can return except for the
  warp's address store (EXT-TMEM-ALLOC-RESULT-ORDER) steps: lane 0 has made the store, so the
  result exists, or lane 0's last event is the allocation, which is ready, and lane 0 makes the
  store (`allocStore_next_steps`), a counted extension.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Progress
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Interface

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Every `tcgen05.alloc` of the kernel requests the immediate 512 columns. -/
theorem kernel_allocN : kernel.code.all (fun ins => match ins.op with
    | .tcAlloc _ _ _ nc => nc == .imm 512
    | _ => true) = true := by
  decide +kernel

/-- **Every recorded allocation returns column 0.** -/
theorem alloc_base (hX : Consistent L kernel asms mem0 X) (hs : ¬ Unsafe L kernel asms mem0 X) :
    ∀ (i : EvId) (pc : Nat) (grp : CtaGroup) (dst : Option Loc) (n cta : Nat)
      (x : Tmem.Pair.Requests) (base : Nat),
      X.get i = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ → x ∈ X.tmemHistory cta →
      x.own.event L 0 = i → x.action = .alloc n base → base = 0 := by
  intro i pc grp dst n cta x base hget hx _ ha
  have hn : n = 512 := by
    rcases get_source hX hget with ⟨f, hf⟩ | ⟨t, ins, o, -, hc, hf⟩
    · cases hf
    · have hop := fires_resource_op hf rfl
      have hall := List.all_eq_true.mp kernel_allocN ins (List.mem_of_getElem? hc)
      generalize hins : ins.op = op at hop hall hf
      cases op <;> simp only [tmemOp, Bool.false_eq_true] at hop hall
      · rename_i grp' b o' nc
        obtain ⟨-, -, m, hm, hact⟩ := fires_tcAlloc_resource hf rfl
        have hnc : nc = .imm 512 := by simpa using hall
        subst hnc
        have hm' : m = truncBits 32 (BitVec.ofInt 64 512) := by
          simp only [readBits, pure, Except.pure, Except.ok.injEq] at hm
          exact hm.symm
        have h512 : m.toNat = 512 := by rw [hm']; decide
        simp only [Tmem.Request.alloc.injEq] at hact
        rw [hact, h512]
      · obtain ⟨-, -, m, a, -, hact⟩ := fires_tcDealloc_resource hf rfl
        cases hact
      · obtain ⟨-, -, hact⟩ := fires_tcRelinquish_resource hf rfl
        cases hact
  subst hn
  exact hX.alloc512_base (tmemNoFault_of_safe
    (fun h : Tmem.Pair.ResourceUnsafe L X => hs (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
      (.inr (.inr (.inr (.inr (.inr (.inr (.inl h)))))))))))))))) cta) hx ha

/-! ### The allocation's address store -/

/-- Prove a statement about the sites of one machine at a list of positions: by cases on the
site, deciding each. -/
local macro "site_cls" : tactic =>
  `(tactic| (intro s h; revert h; cases s <;> (try (rename_i j; revert j)) <;> decide +kernel))

/-- Whether an instruction is the allocation. -/
def allocOp : Op → Bool
  | .tcAlloc .. => true
  | _ => false

/-- The position of the program's allocation. -/
def allocPcs : List Nat := [DStart.Site.alloc.pc]

/-- **The kernel's `tcgen05.alloc` is at one position.** -/
theorem kernel_alloc_pcs : OpPcsFast kernel.code allocOp allocPcs = true := by decide +kernel

theorem dstart_alloc : ∀ s : DStart.Site, s.pc ∈ allocPcs → s = .alloc ∨ s = .allocWr := by
  site_cls
theorem pro_alloc : ∀ s : ProA.Site, s.pc ∈ allocPcs → s ∈ ([] : List ProA.Site) := by site_cls
theorem sm_alloc : ∀ s : Sm.Site, s.pc ∈ allocPcs → s ∈ ([] : List Sm.Site) := by site_cls
theorem epi_alloc : ∀ s : Epi.Site, s.pc ∈ allocPcs → s ∈ ([] : List Epi.Site) := by site_cls
theorem worker_alloc : ∀ s : Worker.Site, s.pc ∈ allocPcs → s ∈ ([] : List Worker.Site) := by
  site_cls
theorem idle_alloc : ∀ s : Worker.Idle.Site, s.pc ∈ allocPcs →
    s ∈ ([] : List Worker.Idle.Site) := by site_cls
theorem loader_alloc : ∀ s : Loader.Site, s.pc ∈ allocPcs → s ∈ ([] : List Loader.Site) := by
  site_cls
theorem mma_alloc : ∀ s : Mma.Site, s.pc ∈ allocPcs → s ∈ ([] : List Mma.Site) := by site_cls
theorem exit_alloc : ∀ s : WComp.ExitSite, s.pc ∈ allocPcs →
    s ∈ ([] : List WComp.ExitSite) := by site_cls

/-- **A thread whose last event is an allocation request is at the allocation's address store,
or is not lane 0 of its warp.** -/
theorem alloc_next (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X) :
    NextFacts Q L X where
  alloc_next := by
    intro g pc grp dst n s hg hget hσ
    have hlen := len_of_get hget
    simp only at hlen
    obtain ⟨d, hd⟩ := Frame.event_state (C := code L Q) hf.sound hX hf.tracked hget
      (by intro pc' f h; cases h)
    obtain ⟨t, ins, o, hat, hinv, hc, hfire⟩ := Frame.fired_site hf.sound hX hget hd
    have hop := fires_resource_op hfire rfl
    have halloc : allocOp ins.op = true := by
      generalize hins : ins.op = op at hop hfire
      cases op <;> simp only [tmemOp, Bool.false_eq_true] at hop
      · rfl
      · obtain ⟨-, -, m, a, -, hact⟩ := fires_tcDealloc_resource hfire rfl
        cases hact
      · obtain ⟨-, -, hact⟩ := fires_tcRelinquish_resource hfire rfl
        cases hact
    have hpc : TSt.pc d ∈ allocPcs := OpPcsFast.mem kernel_alloc_pcs hc halloc
    have hsub0 : TSt.sub d = 0 := by
      have h1 : t.sub = TSt.sub d := hat.2.1
      have h2 : t.sub = 0 := by
        generalize hins : ins.op = op at halloc hfire
        cases op <;> simp only [allocOp, Bool.false_eq_true] at halloc
        exact (fires_tcAlloc_resource hfire rfl).1
      rw [← h1, h2]
    -- the state after the event is the machine's successor of the state before it
    have he : (X.tr g)[(X.tr g).length - 1]? =
        some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ := hget
    have hsucc := Frame.stateAt_succ (C := code L Q) (X := X) (g := g) he
    rw [Nat.sub_add_cancel (by omega)] at hsucc
    change Frame.stateAt (code L Q) X g _ = _ at hσ
    rw [hsucc, hd] at hσ
    simp only [Option.bind_some] at hσ
    have hσ' : (threadCode L g Q).next d ⟨pc, .tc (.resource grp dst (.alloc n))⟩ =
        some (some s) := hσ
    rcases d with d | d
    · rcases d with d | d | d | d
      · -- the common start
        have hpc' : d.site.pc ∈ allocPcs := hpc
        have hsub' : d.site.sub = 0 := hsub0
        have hsite : d.site = .alloc := by
          rcases dstart_alloc _ hpc' with h | h
          · exact h
          · rw [h] at hsub'
            simp [DStart.Site.sub] at hsub'
        by_cases hl : laneOf L g = 0
        · left
          simp only [threadCode, TSt.next, DComp.next, DComp.dstartNext, DStart.next, hsite, hl,
            ↓reduceIte, Option.map_some, Option.some.injEq] at hσ'
          have hne : DStart.Site.allocWr ≠ DStart.Site.toProA := by decide
          simp only [hne, ↓reduceIte] at hσ'
          subst hσ'
          simp only [nextKind, TSt.pc, DComp.pc, TSt.sub, DComp.sub, DStart.Site.sub,
            DStart.Site.pc]
          decide +kernel
        · right
          exact hl
      · exact absurd (pro_alloc d.site hpc) (by simp)
      · exact absurd (sm_alloc d.site hpc) (by simp)
      · exact absurd (epi_alloc d.site hpc) (by simp)
    · rcases d with d | d | d | d | d
      · exact absurd (worker_alloc d.site hpc) (by simp)
      · exact absurd (idle_alloc d.site hpc) (by simp)
      · exact absurd (loader_alloc _ hpc) (by simp)
      · exact absurd (mma_alloc _ hpc) (by simp)
      · exact absurd (exit_alloc d.site hpc) (by simp)


/-- **Lane 0's allocation names the word at the shared base, and its next event, if any, stores
that word at the allocation's site** (the address store, `DStart.Site.allocWr`). -/
theorem alloc_result_event (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g j pc : Nat} {grp : CtaGroup} {dst : Option Loc} {n : Nat}
    (hg : g < L.threads) (hget : X.get (g, j) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩)
    (hlane : laneOf L g = 0) :
    dst = some ⟨.shared, g / L.block, L.sharedBase⟩ ∧ ∀ e, X.get (g, j + 1) = some e →
      ∃ bytes, e = ⟨pc, .wr { loc := ⟨.shared, g / L.block, L.sharedBase⟩, size := 4 } bytes⟩ := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  obtain ⟨d, hd⟩ := Frame.event_state (C := code L Q) hf.sound hX hf.tracked hget
    (by intro pc' f h; cases h)
  obtain ⟨t, ins, o, hat, hinv, hc, hfire⟩ := Frame.fired_site hf.sound hX hget hd
  have hop := fires_resource_op hfire rfl
  have halloc : allocOp ins.op = true := by
    generalize hins : ins.op = op at hop hfire
    cases op <;> simp only [tmemOp, Bool.false_eq_true] at hop
    · rfl
    · obtain ⟨-, -, m, a, -, hact⟩ := fires_tcDealloc_resource hfire rfl
      cases hact
    · obtain ⟨-, -, hact⟩ := fires_tcRelinquish_resource hfire rfl
      cases hact
  have hpc : TSt.pc d ∈ allocPcs := OpPcsFast.mem kernel_alloc_pcs hc halloc
  have hsub0 : TSt.sub d = 0 := by
    have h1 : t.sub = TSt.sub d := hat.2.1
    have h2 : t.sub = 0 := by
      generalize hins : ins.op = op at halloc hfire
      cases op <;> simp only [allocOp, Bool.false_eq_true] at halloc
      exact (fires_tcAlloc_resource hfire rfl).1
    rw [← h1, h2]
  rcases d with d | d
  · rcases d with d | d | d | d
    · have hpc' : d.site.pc ∈ allocPcs := hpc
      have hsub' : d.site.sub = 0 := hsub0
      have hsite : d.site = .alloc := by
        rcases dstart_alloc _ hpc' with h | h
        · exact h
        · rw [h] at hsub'
          simp [DStart.Site.sub] at hsub'
      obtain ⟨u, hF⟩ := fired_cont hX hf hg hget hd (by simp [ExitState])
      have he0 := DStart.shape_alloc hb (ProA.sharedOk_of_pre hpre) (fired_dstart hF) hsite
      simp only [Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at he0
      obtain ⟨hpc0, -, hdst, -⟩ := he0
      refine ⟨hdst, fun e hnext => ?_⟩
      have he : (X.tr g)[j]? = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩ := hget
      have hsucc := Frame.stateAt_succ (C := code L Q) (X := X) (g := g) he
      rw [hd] at hsucc
      simp only [Option.bind_some] at hsucc
      obtain ⟨site, tm⟩ := d
      simp only at hsite
      subst hsite
      have hσ1 : St Q L X g (j + 1) =
          some (some (.d (.dstart ⟨.allocWr, tm⟩))) := by
        change Frame.stateAt (code L Q) X g (j + 1) = _
        rw [hsucc]
        change (threadCode L g Q).next (.d (.dstart ⟨.alloc, tm⟩))
          ⟨pc, .tc (.resource grp dst (.alloc n))⟩ = _
        simp only [threadCode, TSt.next, DComp.next, DComp.dstartNext, DStart.next, hlane,
          ↓reduceIte, Option.map_some, Option.some.injEq]
        have hne : DStart.Site.allocWr ≠ DStart.Site.toProA := by decide
        simp only [hne, ↓reduceIte]
      obtain ⟨u1, hF1⟩ := fired_cont hX hf hg hnext hσ1 (by simp [ExitState])
      obtain ⟨col, -, he1⟩ :=
        DStart.shape_allocWr hb (ProA.sharedOk_of_pre hpre) (fired_dstart hF1) rfl
      exact ⟨_, he1.trans (by rw [hpc0]; rfl)⟩
    · exact absurd (pro_alloc d.site hpc) (by simp)
    · exact absurd (sm_alloc d.site hpc) (by simp)
    · exact absurd (epi_alloc d.site hpc) (by simp)
  · rcases d with d | d | d | d | d
    · exact absurd (worker_alloc d.site hpc) (by simp)
    · exact absurd (idle_alloc d.site hpc) (by simp)
    · exact absurd (loader_alloc _ hpc) (by simp)
    · exact absurd (mma_alloc _ hpc) (by simp)
    · exact absurd (exit_alloc d.site hpc) (by simp)


/-- **An allocation that can return except for its warp's address store steps**: lane 0 of the
warp has made the store after its allocation, which is the result the lane waits for, or lane 0's
last event is the allocation, which can return, and lane 0 makes the store, a counted extension. -/
theorem publish_steps {T : Nat → TSt → Nat} (hpre : Pre Q L mem0) (hc : NextCtx Q L mem0 X)
    (hf : ThreadFacts Q L mem0 X) {i : EvId} {site n : Nat} {group : CtaGroup}
    {dst : Option Loc} (he : X.get i = some ⟨site, .tc (.resource group dst (.alloc n))⟩)
    (hrr : Tmem.Pair.ReturnReady L X i)
    (hMissing : ¬ ∃ store out, Tmem.Pair.AllocResult L X store i out)
    {o : Descent.Obligation} : Sched.Steps (timed T Q L) mem0 X o := by
  have hX := hc.max.1
  have hcov : Tmem.Pair.Covered L X i := hrr.2 ⟨site, group, dst, .alloc n, he, trivial⟩
  obtain ⟨ws, hws, w, hw, lane, rfl⟩ := hcov
  obtain ⟨grp, hv⟩ := hws.valid hX.tmemPair hw
  have hreq := (hv.2.2.1 lane).symm.trans he
  simp only [Option.some.injEq, Event.mk.injEq, Kind.tc.injEq, TcKind.resource.injEq] at hreq
  have halloc := hreq.2.2.2
  have hLead := hv.2.2.1 0
  have hprop := Tmem.Pair.WarpRequest.event_props hv 0
  have hbound : (w.event L 0).1 < L.threads := hprop.2.2
  have hzero : laneOf L (w.event L 0).1 = 0 := by
    have hlt : w.warp * 32 < L.block := by have := hv.2.1; omega
    simp only [laneOf, Tmem.Pair.WarpRequest.event, Fin.val_zero, Nat.add_zero]
    rw [Nat.mul_comm w.cta, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    simp
  have hLead' : X.get (w.event L 0) = some ⟨w.pc, .tc (.resource grp w.dst (.alloc n))⟩ := by
    simpa only [halloc] using hLead
  obtain ⟨hdst, hnextEv⟩ := alloc_result_event hpre hX hf hbound hLead' hzero
  have hindex : (w.event L 0).2 < (X.tr (w.event L 0).1).length := len_of_get hLead'
  by_cases hLater : (w.event L 0).2 + 1 < (X.tr (w.event L 0).1).length
  · have hEvt : X.get ((w.event L 0).1, (w.event L 0).2 + 1) =
        some ((X.tr (w.event L 0).1)[(w.event L 0).2 + 1]'hLater) :=
      List.getElem?_eq_some_iff.mpr ⟨hLater, rfl⟩
    obtain ⟨bytes, hStore⟩ := hnextEv _ hEvt
    exact (hMissing ⟨_, _, Tmem.Pair.AllocResult.of_warpRequest hv halloc hdst rfl hprop.1
      (hEvt.trans (congrArg some hStore)) lane⟩).elim
  · have hlast : (X.tr (w.event L 0).1).length - 1 = (w.event L 0).2 := by omega
    have hLeadLast : X.get ((w.event L 0).1, (X.tr (w.event L 0).1).length - 1) =
        some ⟨w.pc, .tc (.resource grp w.dst (.alloc n))⟩ := by
      rw [hlast]
      exact hLead'
    have hCover : Tmem.Pair.Covered L X (w.event L 0) := ⟨ws, hws, w, hw, 0, rfl⟩
    have hReady := Tmem.Pair.ReturnReady.ready hX.tmemPair hLead'
      ⟨hCover.performed hX.tmemPair, fun _ => hCover⟩ (fun _ _ hl => (hl hzero).elim)
    have hRel : Step.Released L X (w.event L 0).1 := ⟨fun _ _ _ _ => by
      rw [hlast]
      exact hReady⟩
    have hp : Frame.Pending L X (w.event L 0).1 := by
      refine ⟨hbound, no_canceled hX _ hbound, fun pc hl => ?_⟩
      rw [List.getLast?_eq_getElem?] at hl
      have h := hLeadLast.symm.trans hl
      cases h
    cases hσ : St Q L X (w.event L 0).1 (X.tr (w.event L 0).1).length with
    | none =>
      exact Descent.dead_steps_inOrder asms_wfStep hc.max hc.noUb hc.sound hp hσ hRel
    | some σ =>
      cases σ with
      | none => exact absurd hσ (hf.tracked _ _ hbound)
      | some d =>
        rcases hc.facts.alloc_next hbound hLeadLast hσ with hk | hn
        · exact allocStore_next_steps hc hp hσ hk hRel
        · exact (hn hzero).elim


/-- Every `cta_group::1` allocation of thread `g`, if `g` is lane 0 of its warp, is followed by the
store of the allocated address at the allocation's site (EXT-TMEM-ALLOC-RESULT-ORDER). -/
def AllocStored (L : Launch) (X : Execution) (g : Nat) : Prop :=
  ∀ {j pc : Nat} {dst : Option Loc} {n : Nat},
    X.get (g, j) = some ⟨pc, .tc (.resource .one dst (.alloc n))⟩ → laneOf L g = 0 →
    ∃ e, X.get (g, j + 1) = some e ∧ ∃ D bytes, dst = some D ∧ D.space = .shared ∧
      D.cta = g / L.block ∧ e = ⟨pc, .wr { loc := D, size := 4 } bytes⟩

/-- **A thread that is not at the address store has stored every allocation's address**: an
allocation that is not its last event is followed by the store (`alloc_result_event`); a last one
leaves lane 0 at the store (`alloc_next`). -/
theorem allocStored_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) {g : Nat} {d : TSt} (hg : g < L.threads)
    (hσ : St Q L X g (X.tr g).length = some (some d)) (hk : nextKind d ≠ .allocStore) :
    AllocStored L X g := by
  intro j pc dst n hget hlane
  obtain ⟨hdst, hnext⟩ := alloc_result_event hpre hX hf hg hget hlane
  have hj := len_of_get hget
  simp only at hj
  by_cases hlt : j + 1 < (X.tr g).length
  · have he : X.get (g, j + 1) = some ((X.tr g)[j + 1]'hlt) :=
      List.getElem?_eq_some_iff.mpr ⟨hlt, rfl⟩
    obtain ⟨bytes, hb⟩ := hnext _ he
    exact ⟨_, he, _, bytes, hdst, rfl, rfl, hb⟩
  · have hlast : (X.tr g).length - 1 = j := by omega
    rw [← hlast] at hget
    rcases (alloc_next hX hf).alloc_next hg hget hσ with h | h
    · exact (hk h).elim
    · exact (h hlane).elim

end

end PTX.Kernels.InklingRelDecode.Proof.Progress
