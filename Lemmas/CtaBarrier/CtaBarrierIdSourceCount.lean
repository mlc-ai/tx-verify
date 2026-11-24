-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.CtaBarrier.CtaBarrierExecution
public import Lemmas.CtaBarrier.CtaBarrierTraceHistory
public import Lemmas.CtaBarrier.CtaBarrierGeneration
public import Lemmas.Step.ExitLast
public import Lemmas.Order.StageCausalityThread
public import Lemmas.CtaBarrier.CtaBarrierRoundHistory
public import Lemmas.Order.DependencyWitness
public import Mathlib.Data.List.Nodup

@[expose] public section

section
/-! # Order of a CTA's barrier records

`ObjectCoherent` orders the records of one logical barrier `(CTA, id)` with causality
(`ObjectOrder .ctaBar`); exits belong to no barrier's order. Two records of one thread are
therefore ordered when both are arrivals on the same barrier (`cta_records_source_order`);
an arrival precedes its thread's exit record by the checked resource state alone.
Orders across different barrier IDs, or of exits relative to other threads' records, are
not consequences of `Consistent`. -/

namespace PTX
open CtaBarrier

/-- Record `r` is counted by barrier `id`: an arrival on `id`, or an exit (which every
barrier counts). -/
def CtaBarrier.Record.Admits {α : Type} (id : Nat) : Record α → Prop
  | .arrival id' .. => id' = id
  | .exit .. => True


section
variable {L : Launch} {X : Execution}

theorem CtaBarHistoryOk.grid_of_get (hh : CtaBarHistoryOk L X) {c k : Nat}
    {r : Record EvId} (hr : (X.barriers c)[k]? = some r) : c < L.grid := by
  by_contra hn
  rw [hh.1 c (by omega)] at hr
  cases hr

/-- A recorded arrival names one of the sixteen barriers. -/
theorem CtaBarHistoryOk.arrival_id_lt (hh : CtaBarHistoryOk L X) {c k id warp : Nat}
    {count : Option Nat} {lanes : List (Nat × EvId)}
    (hr : (X.barriers c)[k]? = some (.arrival id warp count lanes)) : id < 16 := by
  obtain ⟨last, hlast⟩ := (hh.2 c (hh.grid_of_get hr)).2.2
  obtain ⟨s, t, -, hperf⟩ := run_at_record hlast hr
  have ha : arrive L.block s id warp count = .ok t := by
    simp only [Record.perform] at hperf
    split_ifs at hperf
    exact hperf
  by_contra hn
  simp [arrive, hn, bind, Except.bind, pure, Except.pure, throw] at ha

/-- An arrival of a thread precedes its exit record: the exit removes the thread from every
later arrival of its warp. -/
theorem CtaBarHistoryOk.arrival_before_exit (hh : CtaBarHistoryOk L X) {c k l id warp x : Nat}
    {count : Option Nat} {lanes : List (Nat × EvId)} {e y : EvId}
    (hr : (X.barriers c)[k]? = some (.arrival id warp count lanes))
    (he : e ∈ (Record.arrival id warp count lanes).refs)
    (hq : (X.barriers c)[l]? = some (.exit x y)) (hy : y.1 = e.1) : k < l := by
  have hc := hh.grid_of_get hr
  obtain ⟨last, hlast⟩ := (hh.2 c hc).2.2
  obtain ⟨s, t, hs, ht⟩ := run_at_record hlast hr
  obtain ⟨u, v, hu, hv⟩ := run_at_record hlast hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
  have hlane := (perform_arrival_lanes ht).2.1 p hp
  have hsp := ((hh.2 c hc).2.1 _ (List.mem_of_getElem? hr)) p hp
  have hsx := (hh.2 c hc).2.1 _ (List.mem_of_getElem? hq)
  obtain ⟨hxb, hyx, -⟩ := hsx
  have hxp : x = p.1 := by
    have h1 := hsp.2.1
    have h2 : y.1 = c * L.block + x := hyx
    omega
  subst hxp
  by_contra hn
  rcases Nat.lt_or_eq_of_le (Nat.le_of_not_gt hn) with hlk | hlk
  · have hv' : exitThread L.block u p.1 = .ok v := hv
    obtain ⟨-, -, hex, -⟩ := exit_shape hv'
    have hlen := (List.getElem?_eq_some_iff.mp hq).1
    have hat : At L.block (X.barriers c) (l + 1) v := by
      unfold At
      rw [List.take_succ_eq_append_getElem hlen, (List.getElem?_eq_some_iff.mp hq).2, run_append,
        hu]
      simp only [run, hv, Except.bind]
    have hsub := exited_prefix (by omega) hat hs
    exact hlane.2.2 (hsub (by rw [hex]; exact Finset.mem_insert_self _ _))
  · subst hlk
    rw [hr] at hq
    cases hq

end

/-- Two records of the same logical barrier respect causality between their references. -/
theorem cta_same_barrier_order {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} (hX : Consistent L K A mem0 X)
    {c k l id w w' : Nat} {cnt cnt' : Option Nat} {lanes lanes' : List (Nat × EvId)} {e f : EvId}
    (hr : (X.barriers c)[k]? = some (.arrival id w cnt lanes))
    (hq : (X.barriers c)[l]? = some (.arrival id w' cnt' lanes'))
    (he : e ∈ (Record.arrival id w cnt lanes).refs)
    (hf : f ∈ (Record.arrival id w' cnt' lanes').refs)
    (hp : Relation.TransGen (stageCausality L X) (.thread e, false) (.thread f,
          false)) : k ≤ l := by
  by_contra hn
  have hid := hX.ctaBar.arrival_id_lt hr
  obtain ⟨ev, hev⟩ := hX.ctaBar.ref_present (List.mem_of_getElem? hr) he
  obtain ⟨fv, hfv⟩ := hX.ctaBar.ref_present (List.mem_of_getElem? hq) hf
  have hback : ObjectOrder L X (.ctaBar c ⟨id, hid⟩) (.thread f, false) (.thread e, false) :=
    ⟨rfl, rfl, f, e, rfl, rfl, ⟨fv, hfv⟩, ⟨ev, hev⟩, l, k, _, _, hq, hr, by omega, rfl, rfl, hf, he⟩
  have hsync : SyncObjectOrder L X (.ctaBar c ⟨id, hid⟩) (.thread f, false) (.thread e, false) :=
    hback
  exact hX.object _ _ ((Relation.TransGen.mono (fun _ _ => Or.inl) _ _ hp).tail (.inr hsync))

/-- A checked resource history cannot reverse two source operations of one thread when both
records are counted by the same barrier: two arrivals on one barrier ID, or an arrival before
its thread's exit. Arrivals on different barrier IDs are not ordered by this theorem. -/
theorem cta_records_source_order {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {X : Execution} (hX : Consistent L K A mem0 X)
    {c i j : Nat} {r q : CtaBarrier.Record EvId} {g a b : Nat}
    (hr : (X.barriers c)[i]? = some r) (hq : (X.barriers c)[j]? = some q)
    (he : (g,a) ∈ r.refs) (hf : (g,b) ∈ q.refs) (hab : a < b)
    (hid : ∀ id w cnt lanes, q = .arrival id w cnt lanes → r.Admits id) : i ≤ j := by
  obtain ⟨fv, hfv⟩ := hX.ctaBar.ref_present (List.mem_of_getElem? hq) hf
  obtain ⟨ev, hev⟩ := hX.ctaBar.ref_present (List.mem_of_getElem? hr) he
  have hc := hX.ctaBar.grid_of_get hr
  cases r with
  | exit x y =>
    exfalso
    have hy : y = (g, a) := by simpa only [Record.refs, List.mem_singleton, eq_comm] using he
    subst hy
    obtain ⟨-, -, pc, hexit⟩ := (hX.ctaBar.2 c hc).2.1 _ (List.mem_of_getElem? hr)
    have hg : g < L.threads := by
      by_contra hn
      have := len_of_get hfv
      rw [hX.outside g (by omega)] at this
      simp at this
    have hlast := Execution.exit_last hX hg hexit
    have := len_of_get hfv
    simp only at this
    omega
  | arrival id w cnt lanes =>
    cases q with
    | exit x y =>
      have hy : y = (g, b) := by simpa only [Record.refs, List.mem_singleton, eq_comm] using hf
      subst hy
      exact (hX.ctaBar.arrival_before_exit hr he hq rfl).le
    | arrival id' w' cnt' lanes' =>
      have hii : id = id' := hid id' w' cnt' lanes' rfl
      subst hii
      exact cta_same_barrier_order hX hr hq he hf
        (stageCausality.issue_po hev (po_of_not_access rfl hab (len_of_get hfv)
          (hX.ctaBar.ref_not_access (List.mem_of_getElem? hq) hf)))

end PTX
end

section
namespace PTX
open CtaBarrier
variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}

theorem cta_ref_not_before (hX : Consistent L K A mem0 X) {c i : Nat}
    (hc : c < L.grid) {r : Record EvId} {e : EvId}
    (hr : (X.barriers c)[i]? = some r) (he : e ∈ r.refs) :
    e ∉ ((X.barriers c).take i).flatMap Record.refs := by
  have hlt := (List.getElem?_eq_some_iff.mp hr).1
  have hd : X.barriers c = (X.barriers c).take i ++ r :: (X.barriers c).drop (i+1) := by
    rw [← (List.getElem?_eq_some_iff.mp hr).2,← List.drop_eq_getElem_cons hlt]
    exact (List.take_append_drop i _).symm
  have hn := (hX.ctaBar.2 c hc).1
  rw [hd,List.flatMap_append,List.flatMap_cons] at hn
  intro hp
  exact (List.nodup_append.mp hn).2.2 _ hp _
    (List.mem_append.mpr (.inl he)) rfl

theorem cta_ref_cta (hX : Consistent L K A mem0 X) {c i : Nat}
    (hc : c < L.grid) {r : Record EvId} {e : EvId}
    (hr : (X.barriers c)[i]? = some r) (he : e ∈ r.refs) : e.1 / L.block = c := by
  have hs := (hX.ctaBar.2 c hc).2.1 r (List.mem_of_getElem? hr)
  have localToCta {g : Nat} (hg : g < L.block) (he : e.1 = c * L.block + g) :
      e.1 / L.block = c := by
    have hb : 0 < L.block := by omega
    rw [he,Nat.add_comm,Nat.add_mul_div_right _ _ hb,Nat.div_eq_of_lt hg,Nat.zero_add]
  cases r with
  | exit g f =>
    simp only [Record.refs,List.mem_singleton] at he
    subst f
    exact localToCta hs.1 hs.2.1
  | arrival id w count lanes =>
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
    exact localToCta (hs p hp).1 (hs p hp).2.1

/-- One collective record contains at most one operation of each source thread. -/
theorem cta_record_thread_unique (hX : Consistent L K A mem0 X) {c i : Nat}
    (hc : c < L.grid) {r : Record EvId} {e f : EvId}
    (hr : (X.barriers c)[i]? = some r) (he : e ∈ r.refs) (hf : f ∈ r.refs)
    (hg : e.1 = f.1) : e = f := by
  have hs := (hX.ctaBar.2 c hc).2.1 r (List.mem_of_getElem? hr)
  obtain ⟨last,hlast⟩ := (hX.ctaBar.2 c hc).2.2
  obtain ⟨s,t,_,hp⟩ := run_at_record hlast hr
  cases r with
  | exit g a =>
    simp only [Record.refs,List.mem_singleton] at he hf
    exact he.trans hf.symm
  | arrival id w count lanes =>
    obtain ⟨p,hp',rfl⟩ := List.mem_map.mp he
    obtain ⟨q,hq',rfl⟩ := List.mem_map.mp hf
    have hpn := (perform_arrival_lanes hp).1
    have hpg := (hs p hp').2.1
    have hqg := (hs q hq').2.1
    have heq : p.1 = q.1 := by omega
    exact congrArg Prod.snd (List.inj_on_of_nodup_map hpn hp' hq' heq)

/-- A barrier of a thread in CTA `c` that the thread passed is recorded in the history. -/
theorem cta_bar_recorded (hX : Consistent L K A mem0 X) {c : Nat} {f : EvId} {id pc : Nat}
    {count : Option Nat} (hbar : X.IsBarrier f id count pc) (hfc : f.1 / L.block = c)
    (hpass : f.2 + 1 < (X.tr f.1).length) :
    ∃ (k w : Nat) (cnt : Option Nat) (lanes : List (Nat × EvId)),
      (X.barriers c)[k]? = some (Record.arrival id w cnt lanes) ∧
      f ∈ (Record.arrival id w cnt lanes).refs := by
  obtain ⟨key, hkey, _⟩ := ctaBarDone_of_returned hX hbar hpass
  obtain ⟨count', pc', hbar'⟩ := hkey.2.1
  have hid : key % 16 = id := by
    have h := hbar'.symm.trans hbar
    simp only [Option.some.injEq, Event.mk.injEq, Kind.bar.injEq] at h
    exact h.2.1
  have hgen := hkey.2.2
  rw [hfc, hid] at hgen
  obtain ⟨k, st, w, cnt, lanes, g, hk, -, hmem, -⟩ := hgen
  exact ⟨k, w, cnt, lanes, hk, List.mem_map.mpr ⟨(g, f), hmem, rfl⟩⟩

/-- A `bar.arrive` of a thread with a later recorded barrier operation is recorded, as an
arrival record of its barrier. -/
theorem cta_arrive_recorded (hX : Consistent L K A mem0 X) {c : Nat} (hc : c < L.grid)
    {e f : EvId} {id pc : Nat} {count : Option Nat}
    (hbar : X.get f = some ⟨pc, .bar id count .arrive⟩)
    (he : e ∈ (X.barriers c).flatMap Record.refs) (hfg : f.1 = e.1) (hlt : f.2 < e.2) :
    ∃ (k w : Nat) (cnt : Option Nat) (lanes : List (Nat × EvId)),
      (X.barriers c)[k]? = some (Record.arrival id w cnt lanes) ∧
      f ∈ (Record.arrival id w cnt lanes).refs := by
  have key : ∀ a, a < L.block → (c * L.block + a) / L.block = c := fun a h => by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt h, Nat.zero_add]
  have hce : e.1 / L.block = c ∧ e.2 < (X.tr e.1).length := by
    obtain ⟨q0, hq0, heq0⟩ := List.mem_flatMap.mp he
    have hs0 := (hX.ctaBar.2 c hc).2.1 q0 hq0
    cases q0 with
    | exit g x =>
      simp only [Record.refs, List.mem_singleton] at heq0
      subst heq0
      obtain ⟨hgb, hx, pc', hget⟩ := hs0
      exact ⟨by rw [hx]; exact key g hgb, len_of_get hget⟩
    | arrival id' w cnt lanes =>
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp heq0
      obtain ⟨hpb, hpe, pc', mode, hp'⟩ := hs0 p hp
      exact ⟨by rw [hpe]; exact key p.1 hpb, len_of_get hp'⟩
  have hf := ArriveRecorded.of_consistent (X := X) hX f id count pc hbar (by rw [hfg]; omega)
  rw [hfg, hce.1] at hf
  obtain ⟨q, hq, hfq⟩ := List.mem_flatMap.mp hf
  have hs := (hX.ctaBar.2 c hc).2.1 q hq
  obtain ⟨k, hk, hqk⟩ := List.mem_iff_getElem.mp hq
  cases q with
  | exit g x =>
    simp only [Record.refs, List.mem_singleton] at hfq
    subst hfq
    obtain ⟨-, -, pc', hx⟩ := hs
    rw [hbar] at hx
    cases hx
  | arrival id' w cnt lanes =>
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hfq
    obtain ⟨-, -, pc', mode, hp'⟩ := hs p hp
    have h := hp'.symm.trans hbar
    simp only [Option.some.injEq, Event.mk.injEq, Kind.bar.injEq] at h
    obtain ⟨-, rfl, -, -⟩ := h
    exact ⟨k, w, cnt, lanes, by rw [List.getElem?_eq_getElem hk, hqk],
      List.mem_map.mpr ⟨p, hp, rfl⟩⟩

/-- A barrier reference `f` of the thread of `e` lies in a record before `e`'s record exactly
when it precedes `e` in program order, provided `e`'s record is counted by `f`'s barrier. -/
theorem cta_prefix_ref_iff (hX : Consistent L K A mem0 X) {c i : Nat}
    (hc : c < L.grid) {r : Record EvId} {e f : EvId} {id pc : Nat} {count : Option Nat}
    (hr : (X.barriers c)[i]? = some r) (he : e ∈ r.refs)
    (hbar : X.IsBarArrival f id count pc) (hfg : f.1 = e.1) (hadm : r.Admits id) :
    f ∈ ((X.barriers c).take i).flatMap Record.refs ↔ f.2 < e.2 := by
  obtain ⟨mode, hbar⟩ := hbar
  have barId {q : Record EvId} {id' : Nat} (hq : q ∈ X.barriers c) (hf : f ∈ q.refs)
      (hqa : ∃ w cnt lanes, q = .arrival id' w cnt lanes) : id' = id := by
    obtain ⟨w, cnt, lanes, rfl⟩ := hqa
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hf
    obtain ⟨-, -, pc', _, hbar'⟩ := ((hX.ctaBar.2 c hc).2.1 _ hq) p hp
    have h := hbar'.symm.trans hbar
    simp only [Option.some.injEq, Event.mk.injEq, Kind.bar.injEq] at h
    exact h.2.1
  constructor
  · intro hp
    obtain ⟨q, hq, hf⟩ := List.mem_flatMap.mp hp
    obtain ⟨k, hk, hq'⟩ := List.mem_iff_getElem.mp hq
    have hklen : k < (X.barriers c).length :=
      lt_of_lt_of_le hk (by simp only [List.length_take]; omega)
    have hq : (X.barriers c)[k]? = some q := by
      rw [List.getElem?_eq_getElem hklen]
      congr 1
      simpa only [List.getElem_take] using hq'
    have hki : k < i := by simp only [List.length_take] at hk; omega
    by_contra hn
    by_cases heq : f.2 = e.2
    · exact cta_ref_not_before hX hc hr he ((Prod.ext hfg heq : f = e) ▸ hp)
    · have hf' : (e.1, f.2) ∈ q.refs := by rwa [← (Prod.ext hfg rfl : f = (e.1, f.2))]
      have hord := cta_records_source_order hX hr hq he hf' (by omega) (by
        intro id' w cnt lanes hqa
        rwa [barId (List.mem_of_getElem? hq) hf ⟨w, cnt, lanes, hqa⟩])
      omega
  · intro hlt
    have hsource := hX.ctaBar.ref_present (List.mem_of_getElem? hr) he
    have hfc : f.1 / L.block = c := hfg ▸ cta_ref_cta hX hc hr he
    obtain ⟨k, w, cnt, lanes, hk, hfk⟩ : ∃ (k w : Nat) (cnt : Option Nat)
        (lanes : List (Nat × EvId)), (X.barriers c)[k]? = some (Record.arrival id w cnt lanes) ∧
          f ∈ (Record.arrival id w cnt lanes).refs := by
      cases mode
      · exact cta_bar_recorded hX hbar hfc (by
          have hl := len_of_get hsource.choose_spec
          rw [hfg]
          omega)
      · exact cta_arrive_recorded hX hc hbar
          (List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? hr, he⟩) hfg hlt
    have hf' : (e.1, f.2) ∈ (Record.arrival id w cnt lanes).refs := by
      rwa [← (Prod.ext hfg rfl : f = (e.1, f.2))]
    have hord := cta_records_source_order hX hk hr hf' he hlt (by
      intro id' w' cnt' lanes' hra
      subst hra
      exact (show id' = id from hadm).symm)
    have hki : k < i := by
      rcases Nat.lt_or_eq_of_le hord with h | rfl
      · exact h
      · rw [hk] at hr
        cases hr
        have := congrArg Prod.snd (cta_record_thread_unique hX hc hk hfk he hfg)
        omega
    refine List.mem_flatMap.mpr ⟨_, ?_, hfk⟩
    apply List.mem_iff_getElem.mpr
    refine ⟨k, ?_, ?_⟩
    · simp only [List.length_take]
      have hklen := (List.getElem?_eq_some_iff.mp hk).1
      omega
    · simpa only [List.getElem_take] using (List.getElem?_eq_some_iff.mp hk).2

end PTX
end

section
namespace PTX
open CtaBarrier
variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}

/-- Select source arrivals of one named resource, regardless of participant count. -/
def Execution.isBarId (id : Nat) (e : Event) : Bool := match e.kind with
  | .bar id' .. => id' == id
  | _ => false

def refBarId (X : Execution) (g id : Nat) (e : EvId) : Bool :=
  decide (e.1 = g) && match X.get e with
    | some ev => Execution.isBarId id ev
    | none => false

def sourceBarsId (X : Execution) (g n id : Nat) : List EvId :=
  ((List.range n).map fun i => (g,i)).filter (refBarId X g id)

def CtaBarrier.isWarpIdArrival (id warp : Nat) : Record α → Bool
  | .arrival id' w _ _ => id' == id && w == warp
  | .exit _ _ => false

def CtaBarrier.idArrivals (h : List (Record α)) (id warp : Nat) : Nat :=
  h.countP (isWarpIdArrival id warp)

theorem refBarId_iff {g id : Nat} {e : EvId} : refBarId X g id e = true ↔
    e.1 = g ∧ ∃ count pc, X.IsBarArrival e id count pc := by
  unfold refBarId
  cases hp : X.get e with
  | none => simp [hp,Execution.IsBarArrival]
  | some ev =>
    obtain ⟨pc,kind⟩ := ev
    cases kind <;> simp [Execution.isBarId,Execution.IsBarArrival,hp]

theorem sourceBarsId_length {g n id : Nat} (hn : n ≤ (X.tr g).length) :
    (sourceBarsId X g n id).length = ((X.tr g).take n).countP (Execution.isBarId id) := by
  induction n with
  | zero => simp [sourceBarsId]
  | succ n ih =>
    have hlt : n < (X.tr g).length := by omega
    have hg : X.get (g,n) = some (X.tr g)[n] := List.getElem?_eq_getElem hlt
    have hi := ih (by omega)
    unfold sourceBarsId
    rw [List.range_succ,List.map_append,List.filter_append,List.length_append]
    change (sourceBarsId X g n id).length + _ = _
    rw [hi,List.take_succ_eq_append_getElem hlt,List.countP_append]
    cases hbar : Execution.isBarId id (X.tr g)[n] <;> simp [refBarId,hg,hbar]

theorem sourceBarsId_nodup (X : Execution) (g n id : Nat) : (sourceBarsId X g n id).Nodup := by
  apply List.Nodup.filter
  exact (List.nodup_range (n := n)).map (fun i j h => (Prod.mk.inj h).2)

/-- ID-specific source instances and actual earlier history references coincide, when the
record of `e` is counted by barrier `id`. -/
theorem cta_prefix_barId_members (hX : Consistent L K A mem0 X) {c i id : Nat}
    (hc : c < L.grid) {r : Record EvId} {e : EvId}
    (hr : (X.barriers c)[i]? = some r) (he : e ∈ r.refs) (hadm : r.Admits id) :
    ∀ f, f ∈ (((X.barriers c).take i).flatMap Record.refs).filter (refBarId X e.1 id) ↔
      f ∈ sourceBarsId X e.1 e.2 id := by
  intro f
  constructor
  · intro hf
    obtain ⟨hm,hid⟩ := List.mem_filter.mp hf
    obtain ⟨hfg,count,pc,hbar⟩ := refBarId_iff.mp hid
    have hless := (cta_prefix_ref_iff hX hc hr he hbar hfg hadm).mp hm
    exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨f.2,List.mem_range.mpr hless,
      Prod.ext hfg.symm rfl⟩,hid⟩
  · intro hf
    obtain ⟨hindex,hid⟩ := List.mem_filter.mp hf
    obtain ⟨hfg,count,pc,hbar⟩ := refBarId_iff.mp hid
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hindex
    exact List.mem_filter.mpr ⟨(cta_prefix_ref_iff hX hc hr he hbar rfl hadm).mpr
      (List.mem_range.mp hj),hid⟩

/-- One live lane contributes exactly once to an arrival of its chosen resource. -/
theorem cta_record_barId_count {c localg id : Nat} {r : Record EvId} {s t : State}
    (hsrc : CtaBarSources L X c r) (hp : r.perform L.block s = .ok t)
    (hg : localg < L.block) (hn : localg ∉ s.exited) :
    r.refs.countP (refBarId X (c*L.block+localg) id) =
      if isWarpIdArrival id (localg/32) r then 1 else 0 := by
  cases r with
  | exit g e =>
    obtain ⟨_,_,pc,he⟩ := hsrc
    simp [Record.refs,refBarId,he,Execution.isBarId,isWarpIdArrival]
  | arrival rid warp count lanes =>
    have hl := perform_arrival_lanes hp
    by_cases hid : rid = id
    · subst rid
      have hcount : (Record.arrival id warp count lanes).refs.countP
          (refBarId X (c*L.block+localg) id) = (lanes.map Prod.fst).count localg := by
        simp only [Record.refs,List.count,List.countP_map]
        apply List.countP_congr
        intro p hpl
        obtain ⟨hg',he,pc,_,hbar⟩ := hsrc p hpl
        simp only [Function.comp_apply,refBarId,hbar,Execution.isBarId,beq_self_eq_true,
          Bool.and_true,decide_eq_true_eq,beq_iff_eq]
        omega
      rw [hcount]
      by_cases hw : warp = localg/32
      · rw [List.count_eq_one_of_mem hl.1 (hl.2.2 localg hg hw.symm hn)]
        simp [isWarpIdArrival,hw]
      · have hm : localg ∉ lanes.map Prod.fst := by
          rintro hm
          obtain ⟨p,hp,hg'⟩ := List.mem_map.mp hm
          have hlane := (hl.2.1 p hp).2.1
          rw [hg'] at hlane
          exact hw hlane.symm
        simp [List.count_eq_zero.mpr hm,isWarpIdArrival,hw]
    · have hz : (Record.arrival rid warp count lanes).refs.countP
          (refBarId X (c*L.block+localg) id) = 0 := by
        apply List.countP_eq_zero.mpr
        intro e he
        obtain ⟨p,hpl,rfl⟩ := List.mem_map.mp he
        obtain ⟨_,_,pc,_,hbar⟩ := hsrc p hpl
        simp [refBarId,hbar,Execution.isBarId,hid]
      rw [hz]
      simp [isWarpIdArrival,hid]

private theorem count_id_refs {xs : List (Record EvId)} {pred : EvId → Bool} {id warp : Nat}
    (hp : ∀ q ∈ xs, q.refs.countP pred = if isWarpIdArrival id warp q then 1 else 0) :
    (xs.flatMap Record.refs).countP pred = idArrivals xs id warp := by
  induction xs with
  | nil => rfl
  | cons q qs ih =>
    rw [List.flatMap_cons,List.countP_append,hp q (by simp)]
    have hh := ih (fun r hr => hp r (by simp [hr]))
    rw [hh]
    simp only [idArrivals,List.countP_cons]
    cases h : isWarpIdArrival id warp q <;> simp [Nat.add_comm]

/-- The number of preceding actual arrivals at a chosen ID equals its source
occurrence count. Other named resources do not change this count. -/
theorem cta_prefix_id_arrival_count (hX : Consistent L K A mem0 X) {c i localg id : Nat}
    (hc : c < L.grid) {r : Record EvId} {e : EvId} {s : State}
    (hr : (X.barriers c)[i]? = some r) (he : e ∈ r.refs)
    (hstate : At L.block (X.barriers c) i s) (hg : localg < L.block)
    (hthread : e.1 = c*L.block+localg) (hn : localg ∉ s.exited) (hadm : r.Admits id) :
    idArrivals ((X.barriers c).take i) id (localg/32) =
      ((X.tr e.1).take e.2).countP (Execution.isBarId id) := by
  obtain ⟨last,hlast⟩ := (hX.ctaBar.2 c hc).2.2
  have hcount : (((X.barriers c).take i).flatMap Record.refs).countP (refBarId X e.1 id) =
      idArrivals ((X.barriers c).take i) id (localg/32) := by
    apply count_id_refs
    intro q hq
    obtain ⟨j,hj,hq'⟩ := List.mem_iff_getElem.mp hq
    have hji : j < i := by simp only [List.length_take] at hj; omega
    have hjlen : j < (X.barriers c).length := by simp only [List.length_take] at hj; omega
    have hq : (X.barriers c)[j]? = some q := by
      rw [List.getElem?_eq_getElem hjlen]
      congr 1
      simpa only [List.getElem_take] using hq'
    obtain ⟨u,v,hu,hv⟩ := run_at_record hlast hq
    have hn' : localg ∉ u.exited := fun hm => hn (exited_prefix hji.le hu hstate hm)
    rw [hthread]
    exact cta_record_barId_count ((hX.ctaBar.2 c hc).2.1 q (List.mem_of_getElem? hq)) hv hg hn'
  have hnd : (((X.barriers c).take i).flatMap Record.refs).Nodup := by
    have hh := (hX.ctaBar.2 c hc).1
    rw [←List.take_append_drop i (X.barriers c),List.flatMap_append] at hh
    exact hh.of_append_left
  have hp := (List.perm_ext_iff_of_nodup (hnd.filter (refBarId X e.1 id))
    (sourceBarsId_nodup X e.1 e.2 id)).mpr (cta_prefix_barId_members hX hc hr he hadm)
  have hlen := hp.length_eq
  rw [←List.countP_eq_length_filter] at hlen
  have hsource := hX.ctaBar.ref_present (List.mem_of_getElem? hr) he
  calc
    idArrivals ((X.barriers c).take i) id (localg/32) = _ := hcount.symm
    _ = (sourceBarsId X e.1 e.2 id).length := hlen
    _ = _ := sourceBarsId_length (len_of_get hsource.choose_spec).le

end PTX
end
