-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PrologueAllocationPrefix
public import Core.Tmem.AllocResult
import Lemmas.Flow.AllocTmpl
import Lemmas.Flow.NotTcAny
import Lemmas.Order.Order
import Lemmas.Tmem.AllocResult
import Lemmas.Tmem.AllocResultDependency
import Lemmas.Tmem.TmemPairHistory

public section

/-! # The allocation instance preceding the prologue's shared read-back -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.PrologueAllocation
open PTX PTX.Flow PTX.Proof Tmem.Pair

private theorem prior_to_read {P : Params} {L : Launch} {g : Nat} {s : Site}
    {e : Event} (hs : beforeRead s = true) (hw : warpOf L g = 0)
    (hn : Machine.next P L g (.prologue s) e = some (some (.prologue .allocRead))) :
    s = .alloc ∨ s = .allocStore := by
  cases hs' : s <;> simp [beforeRead, hs'] at hs
  case alloc => exact .inl rfl
  case allocStore => exact .inr rfl
  all_goals
    cases hk : e.kind <;> simp [Machine.next, next, hs', hk, hw] at hn
  case shfl0.shfl _ _ _ _ recv _ =>
    cases recv <;> simp_all
    split_ifs at hn <;> simp at hn
  case shfl1.shfl _ _ _ _ recv _ =>
    cases recv <;> simp_all
    split_ifs at hn <;> simp at hn
  all_goals try split_ifs at hn

private theorem prior_to_store {P : Params} {L : Launch} {g : Nat} {s : Site}
    {e : Event} (hs : beforeRead s = true)
    (hn : Machine.next P L g (.prologue s) e = some (some (.prologue .allocStore))) :
    s = .alloc := by
  cases hs' : s <;> simp [beforeRead, hs'] at hs
  all_goals
    cases hk : e.kind <;> simp [Machine.next, next, hs', hk] at hn
  case shfl0.shfl _ _ _ _ recv _ =>
    cases recv <;> simp_all
    split_ifs at hn <;> simp at hn
  case shfl1.shfl _ _ _ _ recv _ =>
    cases recv <;> simp_all
    split_ifs at hn <;> simp at hn
  all_goals first | rfl | (split_ifs at hn)

private theorem entering_alloc {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L)
    (hq : Frame.stateAt (Machine.code P L) X g i = some (some (.prologue .alloc)))
    (he : X.get (g, i) = some e) :
    X.get (g, i) = some
      ⟨Flow.tmemAlloc_0, .tc (.resource .one (some (allocAddress L g)) (.alloc 512))⟩ := by
  obtain ⟨t, ins, o, hat, _, hcode, hf⟩ := Frame.fired_site hs hX he hq
  change kernel.code[Flow.tmemAlloc_0]? = some ins at hcode
  obtain rfl := Option.some.inj (hcode.symm.trans Flow.code_tmemAlloc_0)
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have ha : t.regs 554 = some (b32 (allocAddress L g).addr) :=
    holds_mem hat.2.2.2.2 (mem_factsFrom (by table_decide : 554 ∈ liveAll 91))
  have hn : t.regs 555 = some (b32 512) :=
    holds_mem hat.2.2.2.2 (mem_factsFrom (by table_decide : 555 ∈ liveAll 91))
  have hsub : t.sub = 0 := hat.2.1
  have hbase := hpre.sharedAlignment
  rw [← hpre.sharedBase] at hbase
  have hfit := sharedBase_lt hpre
  have haddr : (allocAddress L g).addr < 2 ^ 32 := by
    change L.sharedBase + 222752 < 2 ^ 32
    omega
  have halign : (allocAddress L g).addr % 4 = 0 := by
    change (L.sharedBase + 222752) % 4 = 0
    omega
  rw [tcAlloc_tmpl0 hb ha haddr halign hn hsub] at hf
  exact hf.1 ▸ he

private theorem before_alloc_op (s : Site) (hb : beforeRead s = true)
    (ha : s ≠ .alloc) (hw : s ≠ .allocStore) :
    (kernel.code[s.pc]?).any (fun ins => !tcAnyOp ins.op) = true := by
  cases s <;> simp [beforeRead] at hb
  case alloc => exact (ha rfl).elim
  case allocStore => exact (hw rfl).elim
  case init n => fin_cases n <;> decide +kernel
  all_goals decide +kernel

private theorem no_tc_before_alloc {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    {g i : Nat} (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (hi : i < (X.tr g).length)
    (halloc : Frame.stateAt (Machine.code P L) X g i = some (some (.prologue .alloc)))
    (hp : ∀ j < i, ∃ s, beforeRead s = true ∧
      Frame.stateAt (Machine.code P L) X g j = some (some (.prologue s))) :
    ((X.tr g).take i).countP isTcColl = 0 := by
  apply List.countP_eq_zero.mpr
  intro e hm
  rw [List.mem_take_iff_getElem] at hm
  obtain ⟨j, hj, rfl⟩ := hm
  have hjlen := Nat.lt_of_lt_of_le hj (Nat.min_le_right _ _)
  have hj := Nat.lt_of_lt_of_le hj (Nat.min_le_left _ _)
  have he : X.get (g, j) = some (X.tr g)[j] := List.getElem?_eq_getElem hjlen
  obtain ⟨s, hBefore, hstate⟩ := hp j hj
  obtain ⟨t, ins, o, hat, _, hcode, hf⟩ := Frame.fired_site hs hX he hstate
  change kernel.code[s.pc]? = some ins at hcode
  change Fires s.pc (eventTmpl Assumptions.all L g t ins.op) (X.tr g)[j] o at hf
  have notStore : ∀ {k}, k ≤ i →
      Frame.stateAt (Machine.code P L) X g k = some (some (.prologue .allocRead)) → False := by
    intro k hk hr
    rcases Nat.eq_or_lt_of_le hk with rfl | hk
    · rw [halloc] at hr
      cases hr
    · obtain ⟨p, hp', hs'⟩ := hp k hk
      rw [hr] at hs'
      cases hs'
      change false = true at hp'
      cases hp'
  have storeStep {k : Nat} (hk : k < i)
      (hstore : Frame.stateAt (Machine.code P L) X g k = some (some (.prologue .allocStore))) :
      False := by
    have hk' := hk.trans hi
    have he' : X.get (g, k) = some (X.tr g)[k] := List.getElem?_eq_getElem hk'
    have hstep := Frame.stateAt_succ (C := Machine.code P L) (X := X) he'
    rw [hstore] at hstep
    exact notStore (Nat.succ_le_of_lt hk) hstep
  have hk' : ∀ k, (X.tr g)[j].kind ≠ .tc k := by
    by_cases ha : s = .alloc
    · subst s
      have he' := entering_alloc hpre hX hs hstate he
      have hstep := Frame.stateAt_succ (C := Machine.code P L) (X := X) he'
      rw [hstate] at hstep
      change Frame.stateAt (Machine.code P L) X g (j + 1) =
        Machine.next P L g (.prologue .alloc)
          ⟨Flow.tmemAlloc_0, .tc (.resource .one (some (allocAddress L g)) (.alloc 512))⟩ at hstep
      by_cases hl : laneOf L g = 0
      · have hs' : Frame.stateAt (Machine.code P L) X g (j + 1) =
            some (some (.prologue .allocStore)) := by
          rw [hstep]
          simp [Machine.next, next, hl]; rfl
        rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hj) with hji | hji
        · rw [show j + 1 = i from hji, halloc] at hs'
          cases hs'
        · exact (storeStep hji hs').elim
      · exact (notStore (Nat.succ_le_of_lt hj) (by
          rw [hstep]
          simp [Machine.next, next, hl]; rfl)).elim
    by_cases ha' : s = .allocStore
    · subst s
      exact (storeStep hj hstate).elim
    have hop := before_alloc_op s hBefore ha ha'
    rw [hcode, Option.any_some, Bool.not_eq_true'] at hop
    exact fires_notTc hop hf
  cases hev : (X.tr g)[j] with
  | mk tag kind =>
    cases kind
    case tc k => exact (hk' k (congrArg Event.kind hev)).elim
    all_goals simp [isTcColl]

private theorem previous_event {P : Params} {L : Launch} {X : Execution}
    {g j : Nat} {s : Site} {read : Event} (he : X.get (g, j) = some read)
    (hq : Frame.stateAt (Machine.code P L) X g j = some (some (.prologue s)))
    (hp : ∀ k < j, ∃ p, beforeRead p = true ∧
      Frame.stateAt (Machine.code P L) X g k = some (some (.prologue p)))
    (hs : s ≠ .shfl0) :
    ∃ i ev p, i + 1 = j ∧ X.get (g, i) = some ev ∧ beforeRead p = true ∧
      Frame.stateAt (Machine.code P L) X g i = some (some (.prologue p)) ∧
      Machine.next P L g (.prologue p) ev = some (some (.prologue s)) := by
  have hj : 0 < j := by
    by_contra h
    rw [show j = 0 by omega, Frame.stateAt_zero] at hq
    exact hs (by cases hq; rfl)
  have hlt : j - 1 < (X.tr g).length := by
    have hjlen : j < (X.tr g).length := PTX.len_of_get he
    omega
  let ev := (X.tr g)[j - 1]
  have hv : X.get (g, j - 1) = some ev := List.getElem?_eq_getElem hlt
  obtain ⟨p, hb, hstate⟩ := hp (j - 1) (by omega)
  have hnext := Frame.stateAt_succ (C := Machine.code P L) (X := X) hv
  have hj' : j - 1 + 1 = j := by omega
  rw [hj', hstate, hq] at hnext
  exact ⟨j - 1, ev, p, hj', hv, hb, hstate, hnext.symm⟩

section
variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g j : Nat} {ev : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (hw : warpOf L g = 0)
include hpre hX hs hw

private theorem read_predecessor (hl : laneOf L g ≠ 0) (he : X.get (g, j) = some ev)
    (hq : Frame.stateAt (Machine.code P L) X g j = some (some (.prologue .allocRead)))
    (hp : ∀ k < j, ∃ s, beforeRead s = true ∧
      Frame.stateAt (Machine.code P L) X g k = some (some (.prologue s))) :
    ∃ i, i + 1 = j ∧
      X.get (g, i) = some
        ⟨Flow.tmemAlloc_0, .tc (.resource .one (some (allocAddress L g)) (.alloc 512))⟩ ∧
      X.TcK (g, i) 0 := by
  obtain ⟨i, e, p, hij, hget, hb, hstate, hn⟩ := previous_event he hq hp (by decide)
  rcases prior_to_read hb hw hn with rfl | rfl
  · have halloc := entering_alloc hpre hX hs hstate hget
    have hfirst := no_tc_before_alloc hpre hX hs (PTX.len_of_get hget) hstate
      (fun k hk => hp k (by omega))
    exact ⟨i, hij, halloc, ⟨_, halloc, rfl⟩, hfirst⟩
  · obtain ⟨_, _, q, _, ha, hb', hstate', hn'⟩ :=
      previous_event hget hstate (fun k hk => hp k (by omega)) (by decide)
    obtain rfl := prior_to_store hb' hn'
    have he' := entering_alloc hpre hX hs hstate' ha
    rw [ha] at he'
    cases Option.some.inj he'
    simp [Machine.next, next, hl] at hn'

private theorem store_predecessor (hl : laneOf L g = 0) (hsafe : ¬ ResourceUnsafe L X)
    (he : X.get (g, j) = some ev)
    (hq : Frame.stateAt (Machine.code P L) X g j = some (some (.prologue .allocRead)))
    (hp : ∀ k < j, ∃ s, beforeRead s = true ∧
      Frame.stateAt (Machine.code P L) X g k = some (some (.prologue s))) :
    ∃ i, i + 2 = j ∧
      X.get (g, i) = some
        ⟨Flow.tmemAlloc_0, .tc (.resource .one (some (allocAddress L g)) (.alloc 512))⟩ ∧
      X.TcK (g, i) 0 ∧
      X.get (g, i + 1) = some
        ⟨Flow.tmemAlloc_0, .wr ⟨allocAddress L g, 4, false, false, .cta, 0, false⟩
          (b32 0).toBytes⟩ := by
  obtain ⟨k, store, p, hkj, hget, hb, hstate, hn⟩ := previous_event he hq hp (by decide)
  rcases prior_to_read hb hw hn with rfl | rfl
  · have he' := entering_alloc hpre hX hs hstate hget
    rw [hget] at he'
    cases Option.some.inj he'
    simp [Machine.next, next, hl] at hn
  · obtain ⟨i, alloc, q, hik, ha, hb', hstate', hn'⟩ :=
      previous_event hget hstate (fun l hl => hp l (by omega)) (by decide)
    obtain rfl := prior_to_store hb' hn'
    have halloc := entering_alloc hpre hX hs hstate' ha
    have hfirst := no_tc_before_alloc hpre hX hs (PTX.len_of_get ha) hstate'
      (fun l hl => hp l (by omega))
    have hsget : X.get (g, i + 1) = some store := hik ▸ hget
    obtain ⟨tag, hwrite⟩ := alloc_write hpre hX hs hsafe hl hstate' ha hsget
    have htag := Frame.event_pc hs hX hget hstate
    change store.pc = Flow.tmemAlloc_0 at htag
    have heq := Option.some.inj (hsget.symm.trans hwrite)
    rw [heq] at htag
    rw [show tag = Flow.tmemAlloc_0 from htag] at hwrite
    exact ⟨i, by omega, halloc, ⟨⟨_, halloc, rfl⟩, hfirst⟩, hwrite⟩

/-- At a tracked nonleader readback, the completed allocation has already published its
result. Every readback byte has a program source by Core's visibility axiom. -/
theorem readback_has_source (hl : laneOf L g ≠ 0) (he : X.get (g, j) = some ev)
    (hq : Frame.stateAt (Machine.code P L) X g j = some (some (.prologue .allocRead)))
    (hp : ∀ k < j, ∃ s, beforeRead s = true ∧
      Frame.stateAt (Machine.code P L) X g k = some (some (.prologue s))) :
    ∃ store out, X.Writes store { loc := allocAddress L g, size := 4 } out ∧
      (∀ b < 4, modelCausality L X ((allocAddress L g).at b) (.thread store) (.thread (g, j))) ∧
      ∀ b < 4, (X.rf (.thread (g, j)) b).isSome := by
  obtain ⟨i, hij, ha, _⟩ := read_predecessor hpre hX hs hw hl he hq hp
  have hj : j < (X.tr g).length := PTX.len_of_get he
  have hreturned : Returned X (g, i) := by
    simp only [Returned, ha, Kind.resume, TcKind.resume]
    omega
  have hnode := allocResult_witnessed L X (g, i) ha
    (show PTX.laneOf L g ≠ 0 from fun h => hl ((laneOf_core hpre).symm.trans h))
  obtain ⟨ref, _, hfill⟩ := hX.dependency.ready _ hreturned _ hnode
  cases ref with
  | async => exact hfill.elim
  | thread store =>
    obtain ⟨loc, hresult⟩ := hfill
    have hloc : loc = allocAddress L g := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hget, _, _, _⟩ := hresult
      rw [ha] at hget
      have hkind := congrArg Event.kind (Option.some.inj hget)
      have hargs := TcKind.resource.inj (Kind.tc.inj hkind)
      exact Option.some.inj hargs.2.1.symm
    subst loc
    obtain ⟨out, hstore⟩ := hresult.writes
    obtain ⟨bytes, hkind⟩ := alloc_read hpre hX hs hq he
    let a : Acc := { loc := allocAddress L g, size := 4 }
    have hread : X.Reads (g, j) a bytes := by
      obtain ⟨tag, kind⟩ := ev
      change kind = _ at hkind
      subst kind
      exact ⟨tag, he⟩
    have horder : ∀ b < 4,
        modelCausality L X (a.loc.at b) (.thread store) (.thread (g, j)) := by
      intro b hb
      have hcover : a.Covers (a.loc.at b) := Acc.covers_at hb
      exact modelCausality.of_allocResultBefore L
        ⟨i, a.loc, a, bytes, hresult, by omega, hcover, hread, hcover⟩
    refine ⟨store, out, hstore, horder, fun b hb => ?_⟩
    have hvis := hX.hidden (.thread (g, j)) a bytes b (.thread store) a out (.inl hread) hb
      (.inl hstore) (Acc.covers_at hb) (.direct (horder b hb))
    cases hr : X.rf (.thread (g, j)) b <;> simp_all

/-- The representative lane's own readback sees a program write by ordinary program order. -/
theorem leader_readback_has_source (hl : laneOf L g = 0) (hsafe : ¬ ResourceUnsafe L X)
    (he : X.get (g, j) = some ev)
    (hq : Frame.stateAt (Machine.code P L) X g j = some (some (.prologue .allocRead)))
    (hp : ∀ k < j, ∃ s, beforeRead s = true ∧
      Frame.stateAt (Machine.code P L) X g k = some (some (.prologue s))) :
    ∃ store out, X.Writes store { loc := allocAddress L g, size := 4 } out ∧
      (∀ b < 4, modelCausality L X ((allocAddress L g).at b) (.thread store) (.thread (g, j))) ∧
      ∀ b < 4, (X.rf (.thread (g, j)) b).isSome := by
  obtain ⟨i, hij, _, _, hstore⟩ := store_predecessor hpre hX hs hw hl hsafe he hq hp
  obtain ⟨bytes, hkind⟩ := alloc_read hpre hX hs hq he
  let a : Acc := { loc := allocAddress L g, size := 4 }
  let out := (b32 0).toBytes
  have hwrite : X.Writes (g, i + 1) a out := ⟨_, hstore⟩
  have hread : X.Reads (g, j) a bytes := by
    obtain ⟨tag, kind⟩ := ev
    change kind = _ at hkind
    subst kind
    exact ⟨tag, he⟩
  have hbyte : a.Covers (a.loc.at 0) := Acc.covers_at (by change 0 < 4; decide)
  have hpo : po X (g, i + 1) (g, j) :=
    po_of_overlap (.inr (.inl ⟨out, hwrite, rfl⟩)) (.inl ⟨bytes, hread, rfl⟩)
      rfl (by change i + 1 < j; omega) ⟨_, hbyte, hbyte⟩
  have horder : ∀ b : Nat,
      modelCausality L X (a.loc.at b) (.thread (g, i + 1)) (.thread (g, j)) :=
    fun _ => .inl (.single (.inl hpo))
  refine ⟨(g, i + 1), out, hwrite, fun b _ => horder b, fun b hb => ?_⟩
  have hvis := hX.hidden (.thread (g, j)) a bytes b (.thread (g, i + 1)) a out (.inl hread) hb
    (.inl hwrite) (Acc.covers_at hb) (.direct (horder b))
  cases hr : X.rf (.thread (g, j)) b <;> simp_all
end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.PrologueAllocation
