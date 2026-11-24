-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.PrologueAllocResult
import Lemmas.Flow.NotTensor
import Lemmas.Flow.NotRmw
import Lemmas.Flow.NotBulk
import Lemmas.Flow.Region

public section

/-! # Write sources of the allocation read-back -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.PrologueAllocation

open PTX PTX.Flow PTX.Proof AsyncCopy

private def asyncOrAtomicWrite (op : Op) : Bool :=
  bulkOp op || (clcOp op || (atomicOp op || (tensorOp op || tensorStoreOp op)))

set_option maxRecDepth 100000 in
private theorem no_async_or_atomic_op (s : Site) :
    (kernel.code[s.pc]?).any (fun ins => asyncOrAtomicWrite ins.op) = false := by
  cases s
  case init j => fin_cases j <;> decide +kernel
  case handoff j => fin_cases j <;> decide +kernel
  all_goals decide +kernel

set_option maxRecDepth 100000 in
private theorem store_op (s : Site) (h1 : s ≠ .alloc) (h2 : s ≠ .allocStore) :
    (kernel.code[s.pc]?).any (fun ins => writeOp ins.op) = false := by
  cases s
  case alloc => exact (h1 rfl).elim
  case allocStore => exact (h2 rfl).elim
  case init j => fin_cases j <;> decide +kernel
  case handoff j => fin_cases j <;> decide +kernel
  all_goals decide +kernel

private theorem no_async_or_atomic {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    {i : EvId} {e : Event} (he : X.get i = some e)
    (hsite : ∃ s, Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.prologue s))) :
    ∃ (t : TState) (ins : Instr) (o : Option TState) (s : Site),
      Fires s.pc (eventTmpl Assumptions.all L i.1 t ins.op) e o ∧
      bulkOp ins.op = false ∧ clcOp ins.op = false ∧ atomicOp ins.op = false ∧
      tensorOp ins.op = false ∧ tensorStoreOp ins.op = false := by
  obtain ⟨s, hstate⟩ := hsite
  obtain ⟨t, ins, o, _, _, hcode, hfire⟩ := Frame.fired_site hs hX he hstate
  change kernel.code[s.pc]? = some ins at hcode
  have hop := no_async_or_atomic_op s
  rw [hcode, Option.any_some] at hop
  exact ⟨t, ins, o, s, hfire, by simpa [asyncOrAtomicWrite] using hop⟩

/-- A write whose issuing event is in the prologue comes from the allocator result-store site. -/
theorem write_at_allocStore {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    {w : Ref} {a : Acc} {bs : List Byte} (hw : X.MemWrites w a bs)
    (hsite : ∃ s, Frame.stateAt (Machine.code P L) X w.issuer.1 w.issuer.2 =
      some (some (.prologue s))) :
    ∃ i, w = .thread i ∧ X.Writes i a bs ∧
      Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.prologue .allocStore)) := by
  cases w with
  | thread i =>
    rcases hw with ⟨pc, hwrite⟩ | ⟨old, pc, hrmw⟩
    · obtain ⟨s, hstate⟩ := hsite
      refine ⟨i, rfl, ⟨pc, hwrite⟩, ?_⟩
      obtain ⟨t, ins, o, hat, _, hcode, hf⟩ := Frame.fired_site hs hX hwrite hstate
      change kernel.code[s.pc]? = some ins at hcode
      change Fires s.pc (eventTmpl Assumptions.all L i.1 t ins.op) ⟨pc, .wr a bs⟩ o at hf
      by_cases hstore : s = .allocStore
      · simpa only [hstore, Ref.issuer] using hstate
      by_cases hall : s = .alloc
      · subst s
        change kernel.code[Flow.tmemAlloc_0]? = some ins at hcode
        obtain rfl := Option.some.inj (hcode.symm.trans Flow.code_tmemAlloc_0)
        have hsub : t.sub = 0 := hat.2.1
        cases o with
        | none =>
          rcases fires_none_ends hf with ⟨_, h⟩ | h <;> cases h
        | some u =>
          obtain ⟨_, _, h, _⟩ := fires_tcAlloc hsub hf
          cases h
      · have hn := store_op s hall hstore
        rw [hcode, Option.any_some, fires_write_op hf rfl] at hn
        cases hn
    · obtain ⟨_, _, _, _, hf, _, _, hn, _, _⟩ :=
        no_async_or_atomic hX hs hrmw hsite
      rw [fires_rmw_op hf rfl] at hn
      cases hn
  | async i p =>
    cases p <;> try exact hw.elim
    case writeCopy =>
      obtain ⟨_, ⟨_, hi⟩, _⟩ := hw
      obtain ⟨_, _, _, _, hf, hn, _⟩ :=
        no_async_or_atomic hX hs hi hsite
      exact Bool.noConfusion (hn.symm.trans (fires_bulk_op hf rfl))
    case writeElem k =>
      obtain ⟨_, ⟨_, hi⟩, _⟩ := hw
      obtain ⟨_, _, _, _, hf, hn, _⟩ :=
        no_async_or_atomic hX hs hi hsite
      exact Bool.noConfusion (hn.symm.trans (fires_bulk_op hf rfl))
    case writeCta c =>
      obtain ⟨_, _, ⟨_, hi⟩, _⟩ := hw
      obtain ⟨_, _, _, _, hf, _, hn, _⟩ :=
        no_async_or_atomic hX hs hi hsite
      exact Bool.noConfusion (hn.symm.trans (fires_clcIssue_op hf rfl))
    case writeLoad x y k =>
      obtain ⟨_, _, _, _, ⟨_, hi⟩, _⟩ := hw
      obtain ⟨_, _, _, _, hf, _, _, _, hn, _⟩ :=
        no_async_or_atomic hX hs hi hsite
      exact (fires_notTensor (eventTmpl_notTensor hn) hf _ _ rfl).elim
    case writeStore x y k =>
      obtain ⟨_, _, _, _, ⟨_, hi⟩, _⟩ := hw
      obtain ⟨_, _, _, _, hf, _, _, _, _, hn⟩ :=
        no_async_or_atomic hX hs hi hsite
      exact Bool.noConfusion (hn.symm.trans (fires_tensorStore_op hf rfl))

private def allocationLane (L : Launch) (g : Nat) : Site → Prop
  | .elect0 | .elect1 | .init _ | .fence | .alloc | .allocRead => warpOf L g = 0
  | .allocStore => warpOf L g = 0 ∧ laneOf L g = 0
  | _ => True

private theorem allocationLane_next {L : Launch} {g : Nat} {s u : Site} {e : Event}
    (h : allocationLane L g s) (hn : next L g s e = some (some u)) :
    allocationLane L g u := by
  cases s <;> simp only [allocationLane] at h
  case shfl0 | shfl1 =>
    all_goals
      cases hk : e.kind <;> simp [next, hk] at hn
      rename_i recv _
      cases recv <;> simp at hn
      all_goals try split_ifs at hn
      all_goals simp_all [allocationLane]
      all_goals aesop
  case elect0 | elect1 | alloc | allocRead =>
    all_goals
      cases hk : e.kind <;> simp [next, hk] at hn
      all_goals try split at hn
      all_goals try split_ifs at hn
      all_goals try simp at hn
      all_goals simp_all [allocationLane]
      all_goals aesop
  case init j | fence | allocStore | relinquish | barrier | handoff =>
    all_goals simp only [next] at hn
    all_goals try split_ifs at hn
    all_goals simp_all [allocationLane]
    all_goals aesop

variable {P : Params} {L : Launch}

private theorem allocationLane_at {X : Execution} {g i : Nat} (hi : i < (X.tr g).length) {s : Site}
    (h : Frame.stateAt (Machine.code P L) X g i = some (some (.prologue s))) :
    allocationLane L g s := by
  induction i generalizing s with
  | zero =>
    rw [Frame.stateAt_zero] at h
    cases h
    trivial
  | succ i ih =>
    have hlt : i < (X.tr g).length := by omega
    obtain ⟨p, _, _, hp, hnext⟩ := PrologueRoleTrace.previous_prologue hi.le h
    exact allocationLane_next (ih hlt hp) hnext

private def afterStore : Site → Bool
  | .allocRead | .relinquish | .barrier | .handoff _ => true
  | _ => false

private theorem afterStore_next {L : Launch} {g : Nat} {s u : Site} {e : Event}
    (hst : afterStore s = true) (hn : next L g s e = some (some u)) :
    afterStore u = true := by
  cases s <;> simp only [afterStore, Bool.false_eq_true] at hst
  case allocRead =>
    cases hk : e.kind <;> simp [next, hk] at hn
    all_goals try split at hn
    all_goals try split_ifs at hn
    all_goals simp_all [afterStore]
    all_goals aesop
  case relinquish | barrier | handoff =>
    all_goals simp only [next] at hn
    all_goals try split_ifs at hn
    all_goals simp_all [afterStore]
    all_goals aesop

private theorem afterStore_at {X : Execution} {g i j : Nat} (hij : i < j) (hj : j < (X.tr g).length)
    (hstore : Frame.stateAt (Machine.code P L) X g i = some (some (.prologue .allocStore)))
    {s : Site} (h : Frame.stateAt (Machine.code P L) X g j = some (some (.prologue s))) :
    afterStore s = true := by
  induction j generalizing s with
  | zero => omega
  | succ j ih =>
    have hj' : j < (X.tr g).length := by omega
    obtain ⟨p, _, _, hp, hnext⟩ := PrologueRoleTrace.previous_prologue hj.le h
    by_cases heq : j = i
    · subst j
      rw [hstore] at hp
      have heq : p = Site.allocStore := Machine.ThreadD.prologue.inj
        ((Option.some.inj (Option.some.inj hp)).symm)
      subst p
      simp only [next, Option.some.injEq] at hnext
      cases hnext
      rfl
    · have hij' : i < j := by omega
      exact afterStore_next (ih hij' hj' hp) hnext

/-- An allocator store writes four bytes in the issuing thread's CTA. -/
theorem allocStore_footprint {mem0 : Mem0} {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    {i : EvId} {a : Acc} {bs : List Byte} (hw : X.Writes i a bs)
    (hsite : Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.prologue .allocStore))) :
    a.loc = allocAddress L i.1 ∧ a.size = 4 := by
  obtain ⟨tag, he⟩ := hw
  obtain ⟨t, ins, o, hat, _, hcode, hf⟩ := Frame.fired_site hs hX he hsite
  change kernel.code[Flow.tmemAlloc_0]? = some ins at hcode
  obtain rfl := Option.some.inj (hcode.symm.trans Flow.code_tmemAlloc_0)
  have ha : t.regs 554 = some (b32 (L.sharedBase + 222752)) :=
    holds_mem hat.2.2.2.2 (mem_factsFrom (by table_decide : 554 ∈ liveAll 91))
  have hbase := sharedBase_lt hpre
  have hfit : L.sharedBase + 222752 < 2 ^ 32 := by omega
  exact fires_tcAlloc_wr (effAddr_b32 ha hfit) hf a bs rfl

private theorem allocator_thread {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0) (hw : warpOf L g = 0)
    (hl : laneOf L g = 0) :
    g = ctaOf L g * L.block := by
  simp only [warpOf, laneOf, tidOf_eq hpre] at hw hl
  have hd := Nat.div_add_mod (g % 384) 32
  have hlocal : g % L.block = 0 := by
    rw [hpre.block]
    omega
  simpa [ctaOf, hlocal, Nat.mul_comm] using (Nat.div_add_mod g L.block).symm

/-- Each CTA has at most one event at the prologue allocation-store site. -/
theorem prologue_store_unique {mem0 : Mem0} {X : Execution} {i k : EvId} {e f : Event}
    (hpre : Pre P L mem0) (hcta : ctaOf L i.1 = ctaOf L k.1) (he : X.get i = some e)
    (hf : X.get k = some f)
    (hi : Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.prologue .allocStore)))
    (hk : Frame.stateAt (Machine.code P L) X k.1 k.2 = some (some (.prologue .allocStore))) :
    i = k := by
  obtain ⟨g, x⟩ := i
  obtain ⟨h, y⟩ := k
  have hx : x < (X.tr g).length := PTX.len_of_get he
  have hy : y < (X.tr h).length := PTX.len_of_get hf
  have ⟨hwg, hlg⟩ := allocationLane_at hx hi
  have ⟨hwh, hlh⟩ := allocationLane_at hy hk
  have hg := allocator_thread hpre hwg hlg
  have hh := allocator_thread hpre hwh hlh
  have hthread : g = h := hg.trans ((congrArg (· * L.block) hcta).trans hh.symm)
  subst h
  rcases Nat.lt_trichotomy x y with hlt | rfl | hlt
  · have hb := afterStore_at hlt hy hi hk
    cases hb
  · rfl
  · have hb := afterStore_at hlt hx hk hi
    cases hb

/-- The sources of this read-back were issued at prologue sites. -/
@[expose] def ReadbackSourcesInPrologue (P : Params) (L : Launch) (X : Execution)
    (i : EvId) : Prop :=
  ∀ b < 4, ∀ w, X.rf (.thread i) b = some w →
    ∃ s, Frame.stateAt (Machine.code P L) X w.issuer.1 w.issuer.2 =
      some (some (.prologue s))

/-- The actual allocation read-back reads the four bytes of its CTA allocator word. -/
theorem readback_access {mem0 : Mem0} {X : Execution} {g j : Nat} {ev : Event} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hs : GlobalWrites.SoundThreads P L)
    (he : X.get (g, j) = some ev)
    (hq : Frame.stateAt (Machine.code P L) X g j = some (some (.prologue .allocRead))) :
    ∃ bytes, X.MemReads (.thread (g, j)) { loc := allocAddress L g, size := 4 } bytes := by
  obtain ⟨bytes, hkind⟩ := alloc_read hpre hX hs hq he
  obtain ⟨tag, kind⟩ := ev
  change kind = _ at hkind
  subst kind
  exact ⟨bytes, .inl ⟨tag, he⟩⟩

private theorem readback_rf_from_sources {mem0 : Mem0} {X : Execution} {g j : Nat} {ev : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (he : X.get (g, j) = some ev)
    (hq : Frame.stateAt (Machine.code P L) X g j = some (some (.prologue .allocRead)))
    (hprologue : ReadbackSourcesInPrologue P L X (g, j))
    (hex : ∀ b < 4, (X.rf (.thread (g, j)) b).isSome) :
    ∃ store a out, X.Writes store a out ∧
      Frame.stateAt (Machine.code P L) X store.1 store.2 = some (some (.prologue .allocStore)) ∧
      allocAddress L g = allocAddress L store.1 ∧
      ∀ b < 4, X.rf (.thread (g, j)) b = some (.thread store) := by
  obtain ⟨bytes, hread⟩ := readback_access hpre hX hs he hq
  have selected (b : Nat) (hb : b < 4) :
      ∃ i a out, X.rf (.thread (g, j)) b = some (.thread i) ∧ X.Writes i a out ∧
        Frame.stateAt (Machine.code P L) X i.1 i.2 = some (some (.prologue .allocStore)) ∧
        ctaOf L g = ctaOf L i.1 := by
    have hsrc := (hX.rf _ _ _ hread).2 b hb
    cases hr : X.rf (.thread (g, j)) b with
    | none => simpa [hr] using hex b hb
    | some w =>
      rw [hr] at hsrc
      obtain ⟨a, out, hwrite, hcover, _⟩ := hsrc
      obtain ⟨i, rfl, hw, hstate⟩ := write_at_allocStore hX hs hwrite (hprologue b hb w hr)
      have hc := hcover.2.1
      change ctaOf L g = a.loc.cta at hc
      rw [(allocStore_footprint hpre hX hs hw hstate).1] at hc
      exact ⟨i, a, out, rfl, hw, hstate, hc⟩
  obtain ⟨i, a, out, _, hw, hsite, hcta⟩ := selected 0 (by decide)
  refine ⟨i, a, out, hw, hsite, ?_, ?_⟩
  · simp only [allocAddress, hcta]
  · intro b hb
    obtain ⟨k, _, _, hr, hk, hstate, hctak⟩ := selected b hb
    have hi := prologue_store_unique hpre (hctak.symm.trans hcta)
      (Exists.choose_spec hk) (Exists.choose_spec hw) hstate hsite
    exact hr.trans (congrArg (some ∘ Ref.thread) hi)

private theorem prior_to_store {L : Launch} {g : Nat} {s : Site} {e : Event}
    (hn : next L g s e = some (some .allocStore)) : s = .alloc := by
  cases s
  case alloc => rfl
  all_goals
    cases hk : e.kind <;> simp [next, hk] at hn
  case shfl0.shfl _ _ _ _ recv _ | shfl1.shfl _ _ _ _ recv _ =>
    cases recv <;> simp at hn
    all_goals try split_ifs at hn
    all_goals simp at hn
  all_goals repeat' first | split_ifs at hn | split at hn
  all_goals simp at hn

private theorem before_read_predecessor {L : Launch} {g : Nat} {s t : Site} {e : Event}
    (ht : beforeRead t = true ∨ t = .allocRead)
    (hn : next L g s e = some (some t)) : beforeRead s = true := by
  cases s <;> try rfl
  case allocRead =>
    cases hk : e.kind <;> simp [next, hk] at hn
    split at hn <;> try split_ifs at hn
    all_goals cases t <;> simp_all [beforeRead]
  case relinquish =>
    cases t <;> simp_all [next, beforeRead]
  case barrier =>
    simp only [next, Option.some.injEq] at hn
    split_ifs at hn <;> cases t <;> simp_all [beforeRead]
  case handoff =>
    simp [next] at hn

private theorem prior_read_sites {X : Execution} {g j : Nat} (hj : j < (X.tr g).length) {t : Site}
    (ht : beforeRead t = true ∨ t = .allocRead)
    (hq : Frame.stateAt (Machine.code P L) X g j = some (some (.prologue t))) :
    ∀ k < j, ∃ s, beforeRead s = true ∧
      Frame.stateAt (Machine.code P L) X g k = some (some (.prologue s)) := by
  induction j generalizing t with
  | zero => intro k hk; omega
  | succ j ih =>
    have hj' : j < (X.tr g).length := by omega
    obtain ⟨s, _, _, hs, hn⟩ := PrologueRoleTrace.previous_prologue hj.le hq
    have hb := before_read_predecessor ht hn
    intro k hk
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hk) with rfl | hk'
    · exact ⟨s, hb, hs⟩
    · exact ih hj' (.inl hb) hs k hk'

/-- Every byte of the actual read-back is ordered after the CTA allocator store. -/
theorem readback_ordered {mem0 : Mem0} {X : Execution} {g j : Nat} {ev : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (hsafe : ¬ Tmem.Pair.ResourceUnsafe L X)
    (he : X.get (g, j) = some ev)
    (hq : Frame.stateAt (Machine.code P L) X g j = some (some (.prologue .allocRead))) :
    ∃ store out, X.Writes store { loc := allocAddress L g, size := 4 } out ∧
      (∀ b < 4, modelCausality L X ((allocAddress L g).at b) (.thread store) (.thread (g, j))) := by
  have hj := PTX.len_of_get he
  have hw := allocationLane_at hj hq
  have hp := prior_read_sites hj (.inr rfl) hq
  obtain ⟨store, out, hstore, hOrder, _⟩ := if hl : laneOf L g = 0 then
      leader_readback_has_source hpre hX hs hw hl hsafe he hq hp
    else readback_has_source hpre hX hs hw hl he hq hp
  exact ⟨store, out, hstore, hOrder⟩

/-- A safe allocation read-back reaches relinquishment when its actual sources are in the
prologue. Other threads may already have entered their roles. -/
theorem follows_read_of_prologue_sources {mem0 : Mem0} {X : Execution} {g j : Nat} {ev : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (hprologue : ReadbackSourcesInPrologue P L X (g, j))
    (hsafe : ¬ Tmem.Pair.ResourceUnsafe L X) (he : X.get (g, j) = some ev)
    (hq : Frame.stateAt (Machine.code P L) X g j = some (some (.prologue .allocRead))) :
    Frame.stateAt (Machine.code P L) X g (j + 1) = some (some (.prologue .relinquish)) := by
  have hj := PTX.len_of_get he
  have hw := allocationLane_at hj hq
  have hp := prior_read_sites hj (.inr rfl) hq
  obtain ⟨_, _, _, _, hsource⟩ := if hl : laneOf L g = 0 then
      leader_readback_has_source hpre hX hs hw hl hsafe he hq hp
    else readback_has_source hpre hX hs hw hl he hq hp
  obtain ⟨store, _, _, ⟨_, hstore⟩, hstoreState, hcta, hrf⟩ :=
    readback_rf_from_sources hpre hX hs he hq hprologue hsource
  obtain ⟨writer, k⟩ := store
  have hk : k < (X.tr writer).length := PTX.len_of_get hstore
  have hkpos : 0 < k := by
    by_contra hn
    rw [show k = 0 by omega, Frame.stateAt_zero] at hstoreState
    cases hstoreState
  obtain ⟨s, _, ha, hstate, hnext⟩ :=
    PrologueRoleTrace.previous_prologue (show k - 1 + 1 ≤ (X.tr writer).length by omega)
      (by simpa only [show k - 1 + 1 = k by omega] using hstoreState)
  obtain rfl := prior_to_store hnext
  have hlane := (allocationLane_at hk hstoreState).2
  have hs' := hstore
  rw [show k = k - 1 + 1 by omega] at hs'
  have hz := alloc_write hpre hX hs hsafe hlane hstate ha hs'
  rw [← hcta, show k - 1 + 1 = k by omega] at hz
  exact follows_read hpre hX hs hq he hz hrf

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.PrologueAllocation
