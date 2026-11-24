-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.WarpUniform
public import Lemmas.Flow.SegFree

@[expose] public section

/-! # Warp-uniform polls when local steps may jump

`not_warpDivergent_polls` (`Lemmas/Flow/WarpUniform.lean`) reads a poll branch at `pc` as
entered from the poll at `pc - 1`. It assumes every local step lands at the instruction's next
position (`LocalFrame`). A segment an assumption selects (`segmentRule`, THREAD-LOCAL) is one
local step that may continue at any `pc`. The argument needs less: a local step that does not
land at the next position must not land on a poll branch.

* `LocalLands K A L`: every local step of the instruction at `t.pc` lands at its next position
  (`nextPc`) or at a `pc` that is not a poll branch; at a poll branch the record before is then the
  poll (`Walk.poll_before_lands`), which `not_warpDivergent_synced` uses
  (`Lemmas/Flow/PollSynced.lean`). `LocalLands.of_frames` gives it from the premise of
  `not_warpDivergent_polls`.
* `LocalLands.of_rules`: the local rules of the assumptions write only their destinations
  (`RulesFrame`), and every segment lands at its instruction's next position or off the poll
  branches (`SegLandsAll`).
* For the segment constructors: a `pairEvenAt` step lands at the next position
  (`pairEvenAt_segLands`); a `segmentExact` step lands after the instance of a template shape,
  so it lands off the poll branches when no shape started at a site ends at one
  (`Kernel.segStopsOk`, decidable by `decide +kernel`; `segmentExact_segLands`). An assumption
  without segments lands trivially (`SegLands.of_none`). -/

namespace PTX

open PTX.Flow PTX.Proof PTX.EventFrame PTX.Assumption

noncomputable section

/-! ## The premise -/

/-- Every local step of the instruction at the thread's `pc` lands at the instruction's next
position or at a `pc` that is not a poll branch. The local rule of the values an instruction's
changing special registers read (THREAD-SREG) lands the same way: it is a local step of the
instruction too. -/
structure LocalLands (K : Kernel) (A : List Assumption) (L : Launch) : Prop where
  /-- A local step of the instruction lands at its next position or off the poll branches. -/
  step : ∀ g (t : TState) (ins : Instr) (t' : TState), K.code[t.pc]? = some ins →
    execLocalA A L g t ins.op = .ok t' → t'.pc = nextPc ins.op t.pc ∨ K.pollBranch t'.pc = false
  /-- The local rule of the values the instruction's changing special registers read is a local
  step of the instruction, and lands the same way. -/
  sreg : ∀ g (t : TState) (ins : Instr) (vs : List Nat) (t' : TState),
    K.code[t.pc]? = some ins → execLocalA A L g t (ins.op.withSregValues vs) = .ok t' →
    t'.pc = nextPc ins.op t.pc ∨ K.pollBranch t'.pc = false

/-- A local step that keeps the frame lands at the next position, or at a target of a `brx.idx`,
which is not a poll branch. -/
theorem LocalFrame.lands {K : Kernel} {ins : Instr} {t t' : TState}
    (hc : K.code[t.pc]? = some ins) (hf : LocalFrame ins.op t t') :
    t'.pc = nextPc ins.op t.pc ∨ K.pollBranch t'.pc = false := by
  rcases hf.pc with hpc | hpc
  · exact .inl hpc
  · right
    unfold BrxTarget at hpc
    split at hpc
    · rename_i i targets u hop
      have hb := branchTarget_of_brx hc hop hpc
      unfold Kernel.pollBranch
      simp [hb]
    · exact hpc.elim

/-- Replacing the reads of changing special registers by the values read keeps the instruction's
next position. -/
theorem Op.nextPc_withSregValues (op : Op) (vs : List Nat) (pc : Nat) :
    nextPc (op.withSregValues vs) pc = nextPc op pc := by
  cases op <;> rfl

/-- Replacing the reads of changing special registers by the values read keeps whether `pc` is a
target of a `brx.idx`: those instructions read no special register. -/
theorem BrxTarget_withSregValues (op : Op) (vs : List Nat) (pc : Nat) :
    BrxTarget (op.withSregValues vs) pc ↔ BrxTarget op pc := by
  cases op <;> simp [Op.withSregValues, BrxTarget]

/-- The frame of the local rule of the values changing special registers read lands as the
instruction's own step does: the read values change only the sources of the instruction. -/
theorem LocalFrame.lands_sreg {K : Kernel} {ins : Instr} {t t' : TState}
    {vs : List Nat} (hc : K.code[t.pc]? = some ins)
    (hf : LocalFrame (ins.op.withSregValues vs) t t') :
    t'.pc = nextPc ins.op t.pc ∨ K.pollBranch t'.pc = false := by
  rcases hf.pc with hpc | hpc
  · left
    rwa [Op.nextPc_withSregValues] at hpc
  · right
    rw [BrxTarget_withSregValues] at hpc
    unfold BrxTarget at hpc
    split at hpc
    · rename_i i targets u hop
      have hb := branchTarget_of_brx hc hop hpc
      unfold Kernel.pollBranch
      simp [hb]
    · exact hpc.elim

/-- Local steps that keep the frame land at the next position or off the poll branches. -/
theorem LocalLands.of_frames {K : Kernel} {A : List Assumption} {L : Launch}
    (h : ∀ g t op t', execLocalA A L g t op = .ok t' → LocalFrame op t t') :
    LocalLands K A L where
  step g t ins t' hc hex := LocalFrame.lands hc (h g t ins.op t' hex)
  sreg g t ins vs t' hc hex := LocalFrame.lands_sreg hc (h g t (ins.op.withSregValues vs) t' hex)

/-! ## Event steps -/

/-- A special-register read continues at the local rule of the values read, whose landing decides
where the thread goes. -/
theorem sregTmpl_lands {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} {e : Event} {u : TState}
    (hop : (∃ i, op = .int i) ∨ (∃ m, op = .move m) ∨ ∃ c, op = .cvt c)
    (hsreg : ∀ (vs : List Nat) (u' : TState),
      execLocalA A L g t (op.withSregValues vs) = .ok u' →
      u'.pc = nextPc op t.pc ∨ K.pollBranch u'.pc = false)
    (hfire : Fires t.pc (sregTmpl A L g t op) e (some u)) :
    (u.pc = t.pc ∨ u.pc = t.pc + 1) ∨ K.pollBranch u.pc = false := by
  unfold sregTmpl at hfire
  simp only [Fires, Option.some.injEq] at hfire
  obtain ⟨vals, -, -, ho⟩ := hfire
  subst ho
  cases h : execLocalA A L g t (op.withSregValues vals) with
  | error f => exact .inl (.inl rfl)
  | ok u' =>
    rcases hsreg vals u' h with h' | h'
    · rcases hop with ⟨i, rfl⟩ | ⟨m, rfl⟩ | ⟨c, rfl⟩ <;>
        exact .inl (.inr (by simpa only [Op.withSregValues, nextPc] using h'))
    · exact .inr h'

/-- The local rule of the values an instruction's changing special registers read lands as the
instruction's own step does. -/
theorem localSreg_lands {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} {r : RuleId} {e : Event} {u : TState}
    (hop : (∃ i, op = .int i) ∨ (∃ m, op = .move m) ∨ ∃ c, op = .cvt c)
    (hsreg : ∀ (vs : List Nat) (u' : TState),
      execLocalA A L g t (op.withSregValues vs) = .ok u' →
      u'.pc = nextPc op t.pc ∨ K.pollBranch u'.pc = false)
    (hfire : Fires t.pc (localSregTmpl A L g t r op) e (some u)) :
    (u.pc = t.pc ∨ u.pc = t.pc + 1) ∨ K.pollBranch u.pc = false := by
  cases r <;> simp only [localSregTmpl] at hfire
  case threadInt | threadMove | threadCvt => exact sregTmpl_lands hop hsreg hfire
  all_goals
    simp only [Fires] at hfire
    obtain ⟨-, h⟩ := hfire
    cases h

/-- An event step leaves the thread at its position or the next one, unless it reads changing
special registers: the local rule of the values read then decides, and lands as a local step of
the instruction does (`LocalLands.sreg`). -/
theorem eventTmpl_lands {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {op : Op} {e : Event} {u : TState}
    (hsreg : ∀ (vs : List Nat) (u' : TState),
      execLocalA A L g t (op.withSregValues vs) = .ok u' →
      u'.pc = nextPc op t.pc ∨ K.pollBranch u'.pc = false)
    (hfire : Fires t.pc (eventTmpl A L g t op) e (some u)) :
    (u.pc = t.pc ∨ u.pc = t.pc + 1) ∨ K.pollBranch u.pc = false := by
  cases op <;> simp only [eventTmpl] at hfire
  case mem => exact .inl (callbackFrame_fires mem_frame hfire)
  case warp => exact .inl (callbackFrame_fires warp_frame hfire)
  case matrix => exact .inl (callbackFrame_fires matrix_frame hfire)
  case barSync | barSyncN | barArrive => exact .inl (callbackFrame_fires bar_frame hfire)
  case cluster =>
    simp only [Fires, Option.some.injEq] at hfire
    obtain ⟨-, ho⟩ := hfire
    subst ho
    exact .inl (.inr rfl)
  case setMaxReg => exact .inl (callbackFrame_fires setMaxNReg_frame hfire)
  case cpTensor => exact .inl (callbackFrame_fires tensor_frame hfire)
  case prefetchTensor | prefetchBulk => exact .inl (callbackFrame_fires tensorPrefetch_frame hfire)
  case cpAsync | cpAsyncCommit | cpAsyncWait | cpAsyncArrive =>
    exact .inl (callbackFrame_fires cpAsync_frame hfire)
  case asyncStore => exact .inl (callbackFrame_fires asyncStore_frame hfire)
  case cpTensorStore | bulkCommit | bulkWait =>
    exact .inl (callbackFrame_fires tensorStore_frame hfire)
  case clcTryCancel | clcQuery => exact .inl (callbackFrame_fires clc_frame hfire)
  case fence => exact .inl (callbackFrame_fires fence_frame hfire)
  case mbarInit | mbarInval | fenceMbarInit | mbarArrive | mbarWait | cpBulk =>
    exact .inl (callbackFrame_fires (widen_frame tma_frame) hfire)
  case tcCommit => exact .inl (callbackFrame_fires tcCommit_frame hfire)
  case tcLd => exact .inl (callbackFrame_fires tcLd_frame hfire)
  case tcSt => exact .inl (callbackFrame_fires tcSt_frame hfire)
  case tcAlloc | tcDealloc | tcRelinquish | tcMma | tcFenceBefore | tcFenceAfter | tcWaitLd |
      tcWaitSt | tcCp | tcShift => exact .inl (callbackFrame_fires tc_frame hfire)
  case int i =>
    simp only [Op.rule] at hfire
    split at hfire
    · exact localSreg_lands (.inl ⟨i, rfl⟩) hsreg hfire
    · exact absurd hfire.2 (by simp)
  case move m =>
    simp only [Op.rule] at hfire
    split at hfire
    · exact localSreg_lands (.inr (.inl ⟨m, rfl⟩)) hsreg hfire
    · exact absurd hfire.2 (by simp)
  case cvt c =>
    simp only [Op.rule] at hfire
    split at hfire
    · exact localSreg_lands (.inr (.inr ⟨c, rfl⟩)) hsreg hfire
    · exact absurd hfire.2 (by simp)
  all_goals
    simp only [Fires] at hfire
    obtain ⟨-, h⟩ := hfire
    cases h

/-! ## Walks -/

section Walks
variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- A step into a poll branch comes from the position before it. -/
theorem wstep_into_lands {s s' : TState} {ev : Option Event} (hs : WStep K A L g s ev s')
    (hloc : LocalLands K A L) (hpb : K.pollBranch s'.pc = true) {ins : Instr}
    (hc : K.code[s'.pc]? = some ins) (hl : ins.op.isLocal = true) : s.pc + 1 = s'.pc := by
  have hnt := (pollBranch_spec hpb).2.1
  rcases hs with ⟨-, ht⟩ | ⟨e, -, he⟩
  · unfold Tau out at ht
    cases hf : s.fault with
    | some f => simp [hf] at ht
    | none =>
      simp only [hf] at ht
      cases hc' : K.code[s.pc]? with
      | none => simp [hc'] at ht
      | some ins' =>
        simp only [hc'] at ht
        cases hg : guardHolds s ins'.guard with
        | error f => simp [hg] at ht
        | ok b =>
          cases b with
          | false =>
            simp only [hg, Out.tau.injEq] at ht
            subst ht
            rfl
          | true =>
            simp only [hg] at ht
            split at ht
            · split at ht
              · rename_i t1 hex
                simp only [Out.tau.injEq] at ht
                subst ht
                rcases hloc.step g s ins' t1 hc' hex with hpc | hpc
                · unfold nextPc at hpc
                  split at hpc
                  · rename_i tgt u hop
                    rw [hpc] at hnt hc
                    rw [branchTarget_of hc' hop] at hnt
                    cases hnt
                  · exact hpc.symm
                · rw [hpc] at hpb
                  cases hpb
              · cases ht
            · cases ht
  · obtain ⟨ins', hc', hl', hfire⟩ := estep_event_source he
    rcases eventTmpl_lands (K := K) (A := A) (L := L) (g := g) (t := s) (op := ins'.op) (e := e)
      (u := s') (fun vs u' hex => hloc.sreg g s ins' vs u' hc' hex) hfire with
      (hpc | hpc) | hpb'
    · rw [hpc] at hc
      rw [hc] at hc'
      cases hc'
      rw [hl] at hl'
      cases hl'
    · exact hpc.symm
    · rw [hpb'] at hpb
      cases hpb

/-- At a poll branch, the record before is the poll's event. -/
theorem Walk.poll_before_lands {es : List Event} {vs : List Visit}
    (h : Walk K A L g {} es vs) (hloc : LocalLands K A L) {i : Nat} {v : Visit}
    (hv : vs[i]? = some v) (hb : K.pollBranch v.pc = true) :
    0 < i ∧ ∃ u m p ok acq sc, vs[i - 1]? = some u ∧
      u.ev = some ⟨v.pc - 1, .wait m p ok acq sc⟩ := by
  obtain ⟨h0, -, dst, neg, tgt, base, off, par, acq, sc, hcb, hcw⟩ := pollBranch_spec hb
  have hi : 0 < i := by
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · have := h.zero_pc hv
      simp only at this
      omega
    · exact hi
  refine ⟨hi, ?_⟩
  obtain ⟨u, hu⟩ : ∃ u, vs[i - 1]? = some u := by
    have := (List.getElem?_eq_some_iff.mp hv).1
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hv' : vs[i - 1 + 1]? = some v := by rwa [Nat.sub_add_cancel hi]
  obtain ⟨s, ev, s', ev', rfl, rfl, hst⟩ := h.step_at hu hv'
  simp only [visit_pc] at hb hcb hcw h0 ⊢
  have hpc := wstep_into_lands hst hloc hb hcb rfl
  rw [← hpc, Nat.add_sub_cancel] at hcw
  obtain ⟨m, p, ok, sc', rfl, -⟩ := wstep_poll hst hcw
  refine ⟨_, m, p, ok, acq, sc', hu, ?_⟩
  simp only [visit_ev, ← hpc, Nat.add_sub_cancel]

end Walks

/-! ## Discharging the premise -/

/-- Every segment the assumption selects lands at the next position of the instruction it
starts at, or at a `pc` that is not a poll branch. -/
def SegLands (K : Kernel) (a : Assumption) : Prop :=
  ∀ L g (t t' : TState), a.segmentRule L g t = some (.ok t') →
    (∃ ins, K.code[t.pc]? = some ins ∧ t'.pc = nextPc ins.op t.pc) ∨ K.pollBranch t'.pc = false

/-- Every assumption of the list lands its segments (`SegLands`). -/
def SegLandsAll (K : Kernel) (A : List Assumption) : Prop := ∀ a ∈ A, SegLands K a

/-- An assumption that selects no segment. -/
theorem SegLands.of_none {K : Kernel} {a : Assumption}
    (h : ∀ L g (t : TState), a.segmentRule L g t = none) : SegLands K a := by
  intro L g t t' ht
  rw [h] at ht
  cases ht

theorem SegLandsAll.nil {K : Kernel} : SegLandsAll K [] := nofun

theorem SegLandsAll.cons {K : Kernel} {a : Assumption} {A : List Assumption}
    (ha : SegLands K a) (h : SegLandsAll K A) : SegLandsAll K (a :: A) := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact ha
  · exact h b hb

/-- A segment step continues at the end of the instance. -/
theorem execSegment_pc {σ : Type} [DecidableEq σ] {fn : ℝ → ℝ} {m : SegMatch σ}
    {t t' : TState} (h : execSegment fn m t = .ok t') : t'.pc = m.stop := by
  unfold execSegment at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | cases h; rfl
    | simp_all

/-- The peer-bit step continues at the next position. -/
theorem execPairEven_pc {L : Launch} {g d a : Nat} {t t' : TState}
    (h : execPairEven L g t d a = .ok t') : t'.pc = t.pc + 1 := by
  unfold execPairEven at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | cases h; rfl
    | simp_all

/-- No instance of a template shape started at a site ends at a poll branch. -/
def Kernel.segStopsOk {σ : Type} (K : Kernel) (T : SegTemplate σ) (sites : List Nat) : Bool :=
  sites.all fun pc => T.shapes.all fun sh => !K.pollBranch (pc + sh.body.length)

/-- A `segmentExact` whose shapes started at its sites end off the poll branches lands its
segments. -/
theorem segmentExact_segLands {σ : Type} [DecidableEq σ] {K : Kernel} {name why : String}
    {T : SegTemplate σ} {sites : List Nat} (h : K.segStopsOk T sites = true) :
    SegLands K (segmentExact K name T sites why) := by
  intro L g t t' ht
  right
  simp only [segmentExact] at ht
  split_ifs at ht with hs
  obtain ⟨m, hm, hex⟩ := Option.map_eq_some_iff.mp ht
  rw [execSegment_pc hex]
  unfold SegTemplate.matchAt at hm
  obtain ⟨sh, hsh, hm'⟩ := List.exists_of_findSome?_eq_some hm
  obtain ⟨asg, -, rfl⟩ := Option.map_eq_some_iff.mp hm'
  have hs' : t.pc ∈ sites := by simpa using hs.1
  have := List.all_eq_true.mp (List.all_eq_true.mp h t.pc hs') sh hsh
  simpa using this

/-- A `pairEvenAt` lands its segments at the next position. -/
theorem pairEvenAt_segLands {K : Kernel} {name why : String} {sites : List Nat} :
    SegLands K (pairEvenAt K name sites why) := by
  intro L g t t' ht
  left
  simp only [pairEvenAt] at ht
  split_ifs at ht
  split at ht
  · rename_i d a m hc
    split_ifs at ht
    exact ⟨_, hc, execPairEven_pc (Option.some.inj ht)⟩
  · cases ht

/-- An assumption without local rules keeps `RulesFrame`. -/
theorem RulesFrame.cons_none {a : Assumption} {A : List Assumption}
    (ha : ∀ L g t op, a.localRule L g t op = none) (h : RulesFrame A) : RulesFrame (a :: A) := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · intro L g t op t' hr
    rw [ha] at hr
    cases hr
  · exact h b hb

/-- A local step of an instruction, or of the local rule of the values its changing special
registers read, lands at the instruction's next position or off the poll branches. -/
theorem LocalLands.of_rules_step {K : Kernel} {A : List Assumption} {L : Launch}
    (hF : RulesFrame A) (hS : SegLandsAll K A) {g : Nat} {t : TState} {ins : Instr} {op : Op}
    {t' : TState} (hc : K.code[t.pc]? = some ins)
    (hop : op = ins.op ∨ ∃ vs, op = ins.op.withSregValues vs)
    (h : execLocalA A L g t op = .ok t') :
    t'.pc = nextPc ins.op t.pc ∨ K.pollBranch t'.pc = false := by
  cases hf : A.findSome? (fun a => a.segmentRule L g t) with
  | some r =>
    unfold execLocalA at h
    rw [hf] at h
    subst h
    obtain ⟨a, ha, hr⟩ := List.exists_of_findSome?_eq_some hf
    rcases hS a ha L g t t' hr with ⟨ins', hc', hpc⟩ | hpb
    · rw [hc] at hc'
      cases hc'
      exact .inl hpc
    · exact .inr hpb
  | none =>
    rw [execLocalA_noSegment (List.findSome?_eq_none_iff.mp hf)] at h
    unfold execLocalRule at h
    cases hf' : A.findSome? (fun a => a.localRule L g t op) with
    | none =>
      simp only [hf'] at h
      rcases hop with rfl | ⟨vs, rfl⟩
      · exact LocalFrame.lands hc (execLocal_frame h)
      · exact LocalFrame.lands_sreg hc (execLocal_frame h)
    | some r =>
      simp only [hf'] at h
      obtain ⟨a, ha, hr⟩ := List.exists_of_findSome?_eq_some hf'
      rw [h] at hr
      rcases hop with rfl | ⟨vs, rfl⟩
      · exact LocalFrame.lands hc (hF a ha L g t ins.op t' hr)
      · exact LocalFrame.lands_sreg hc (hF a ha L g t (ins.op.withSregValues vs) t' hr)

/-- **Local steps land** when the assumptions' local rules write only their destinations and
their segments land at the next position or off the poll branches. -/
theorem LocalLands.of_rules {K : Kernel} {A : List Assumption} {L : Launch}
    (hF : RulesFrame A) (hS : SegLandsAll K A) : LocalLands K A L where
  step _ _ _ _ hc h := LocalLands.of_rules_step hF hS hc (Or.inl rfl) h
  sreg _ _ _ _ _ hc h := LocalLands.of_rules_step hF hS hc (Or.inr ⟨_, rfl⟩) h

end

end PTX
