-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.CausalObjectWaitCount
public import Lemmas.Order.ObjectThreadWaitWindowCount

@[expose] public section

/-! # Thread counts on one object

A proof tool. Before a thread's record at position `i` of one mbarrier object, the object's
history contains exactly that thread's records with smaller trace index
(`Consistent.object_thread_take_mem_iff`). Its successful waits and its arrivals there
therefore count the thread's earlier source operations on that object. Only that object's
history and causality are used; no other object's order, no safety premise and no global
protocol order. Arrivals are counted with their fault records kept, while a successful wait
is counted only in a fault-free prefix.
-/
namespace PTX
noncomputable section
open AsyncCopy

/-- Whether event `e` is an arrival on `m`. -/
def sourceArrive (m : Loc) (e : Event) : Bool := match e.kind with
  | .arrive m' _ _ _ _ => decide (m' = m)
  | _ => false

/-- Whether record `q` is thread `g`'s arrival. -/
def threadArrival (g : Nat) (q : MBarrier.Record Ref) : Bool :=
  objectThreadSelected g q.id && (match q.action with | .arrive _ _ => true | _ => false)

theorem threadArrival_iff {g : Nat} {q : MBarrier.Record Ref} :
    threadArrival g q = true ↔
      objectThreadSelected g q.id = true ∧ ∃ c t, q.action = .arrive c t := by
  cases hact : q.action with
  | init _ => simp [threadArrival, hact]
  | completeTx _ => simp [threadArrival, hact]
  | arrive _ _ => simp [threadArrival, hact]
  | pollParity _ _ => simp [threadArrival, hact]
  | inval => simp [threadArrival, hact]
  | increment => simp [threadArrival, hact]

private theorem countP_take_eq_range_ctc {α : Type} (pred : α → Bool) (xs : List α) (k : Nat) :
    (xs.take k).countP pred = (List.range k).countP (fun j => xs[j]?.any pred) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.take_add_one,List.range_succ,List.countP_append,List.countP_append,ih]
    cases hg : xs[k]? <;> simp [hg]

private theorem sourceArrive_objectAction {X : Execution} {m : Loc} {g j : Nat}
    (hs : (X.get (g,j)).any (sourceArrive m) = true) :
    ∃ c t, objectAction X X.async m (.thread (g,j)) = some (.arrive c t) := by
  cases he : X.get (g,j) with
  | none => simp only [he,Option.any_none,Bool.false_eq_true] at hs
  | some ev =>
    obtain ⟨_,kind⟩ := ev
    cases kind
    case arrive target tx count _ _ =>
      have ht : target = m := by simpa [he,sourceArrive] using hs
      subst ht
      exact ⟨count,tx,by simp [objectAction,he]⟩
    all_goals simp [he,sourceArrive] at hs

private theorem objectAction_sourceArrive {X : Execution} {m : Loc} {g j c t : Nat}
    (ha : objectAction X X.async m (.thread (g,j)) = some (.arrive c t)) :
    (X.get (g,j)).any (sourceArrive m) = true := by
  obtain ⟨ev,he⟩ := objectAction_present ha
  obtain ⟨_,kind⟩ := ev
  cases kind <;> simp only [objectAction,he] at ha
  case arrive target tx count _ _ =>
    by_cases hm : target = m
    · subst hm
      simp [he,sourceArrive]
    · simp [hm] at ha
  case asyncArrive target noinc =>
    cases noinc
    · simp only at ha; split_ifs at ha; cases ha
    · cases ha
  all_goals first
    | (split_ifs at ha; cases ha)
    | cases ha

/-- Window form of the arrival count: a duplicate-free window of one object that holds
exactly thread `g`'s records below `k` counts that thread's arrivals on the object among
its first `k` events. Arrival actions are fixed by their source even when the reply
faults, so no fault premise is needed. -/
theorem Consistent.object_thread_arrival_count_window {L : Launch} {K : Kernel}
    {A : List Assumption} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L K A mem0 X) {m : Loc} {g k : Nat} (prior : List (MBarrier.Record Ref))
    (hsub : ∀ q ∈ prior, q ∈ X.objects m) (hnodup : (prior.map MBarrier.Record.id).Nodup)
    (hwin : ∀ q j, q ∈ X.objects m → q.id = .thread (g,j) → (q ∈ prior ↔ j < k)) :
    prior.countP (threadArrival g) = ((X.tr g).take k).countP (sourceArrive m) := by
  let source := fun j => (X.get (g,j)).any (sourceArrive m)
  let actualIds := (prior.filter (threadArrival g)).map MBarrier.Record.id
  let sourceIds := ((List.range k).filter source).map (fun j => Ref.thread (g,j))
  have haNodup : actualIds.Nodup := hnodup.sublist (List.filter_sublist.map _)
  have hsNodup : sourceIds.Nodup := by
    apply ((List.nodup_range (n := k)).filter source).map
    intro i j he
    exact congrArg (fun id => id.issuer.2) he
  have hmem : ∀ id, id ∈ actualIds ↔ id ∈ sourceIds := by
    intro id
    constructor
    · intro hid
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hid
      obtain ⟨hq,harr⟩ := List.mem_filter.mp hq
      obtain ⟨hsel,c,t,hact⟩ := threadArrival_iff.mp harr
      obtain ⟨j,hqid⟩ := objectThreadSelected_iff.mp hsel
      have hj : j < k := (hwin q j (hsub q hq) hqid).mp hq
      have hobj := ((hX.tma.2.2.1 m).2.1 q (hsub q hq)).1
      rw [hqid,hact] at hobj
      exact List.mem_map.mpr ⟨j,List.mem_filter.mpr ⟨List.mem_range.mpr hj,
        objectAction_sourceArrive hobj⟩,hqid.symm⟩
    · intro hid
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hid
      obtain ⟨hjr,hs⟩ := List.mem_filter.mp hj
      obtain ⟨c,t,ha⟩ := sourceArrive_objectAction hs
      obtain ⟨q,hq,hqid⟩ := (hX.tma.2.2.1 m).2.2 (.thread (g,j)) (.arrive c t) ha
      have hp : q ∈ prior := (hwin q j hq hqid).mpr (List.mem_range.mp hjr)
      have hact : q.action = .arrive c t := by
        have hobj := ((hX.tma.2.2.1 m).2.1 q hq).1
        rw [hqid,ha] at hobj
        exact (Option.some.inj hobj).symm
      apply List.mem_map.mpr
      refine ⟨q,List.mem_filter.mpr ⟨hp,threadArrival_iff.mpr
        ⟨objectThreadSelected_iff.mpr ⟨j,hqid⟩,c,t,hact⟩⟩,hqid⟩
  have hperm : actualIds.Perm sourceIds := (List.perm_ext_iff_of_nodup haNodup hsNodup).mpr hmem
  calc
    prior.countP (threadArrival g) = actualIds.length := by
      rw [List.countP_eq_length_filter]
      exact (List.length_map _).symm
    _ = sourceIds.length := hperm.length_eq
    _ = ((X.tr g).take k).countP (sourceArrive m) := by
      rw [countP_take_eq_range_ctc,List.countP_eq_length_filter]
      exact List.length_map _

/-- The records of thread `g` before position `i` of object `m`, where the thread's record
at `i` has trace index `k`, are exactly its records with trace index below `k`. -/
theorem Consistent.object_thread_take_mem_iff {L : Launch} {K : Kernel}
    {A : List Assumption} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L K A mem0 X) {m : Loc} {i g k : Nat} {r : MBarrier.Record Ref}
    (hi : (X.objects m)[i]? = some r) (hrid : r.id = .thread (g,k))
    {q : MBarrier.Record Ref} {j : Nat} (hq : q ∈ X.objects m) (hqid : q.id = .thread (g,j)) :
    q ∈ (X.objects m).take i ↔ j < k := by
  obtain ⟨l,hl⟩ := List.mem_iff_getElem?.mp hq
  have hidx := hX.object_thread_index_iff hl hi hqid hrid
  constructor
  · intro hmem
    obtain ⟨l',hl',he⟩ := List.mem_take_iff_getElem.mp hmem
    have hl'' : (X.objects m)[l']? = some q := by
      rw [List.getElem?_eq_getElem (by omega), he]
    have := ObjectInit.checked_record_index_eq (hX.tma.2.2.1 m).1 hl hl'' rfl
    exact hidx.mp (by omega)
  · intro hjk
    have hli := hidx.mpr hjk
    obtain ⟨hlen,hv⟩ := List.getElem?_eq_some_iff.mp hl
    exact List.mem_take_iff_getElem.mpr ⟨l,by omega,hv⟩

/-- Arrivals of thread `g` before its record at position `i` of object `m` equal its
arrivals on `m` among the first `k` events. Needs no fault-free premise. -/
theorem Consistent.object_thread_arrival_count_before {L : Launch} {K : Kernel}
    {A : List Assumption} {mem0 : Mem0} {X : Execution}
    (hX : Consistent L K A mem0 X) {m : Loc} {i g k : Nat} {r : MBarrier.Record Ref}
    (hi : (X.objects m)[i]? = some r) (hrid : r.id = .thread (g,k)) :
    ((X.objects m).take i).countP (threadArrival g) =
      ((X.tr g).take k).countP (sourceArrive m) :=
  hX.object_thread_arrival_count_window _ (fun _ hq => List.mem_of_mem_take hq)
    ((hX.tma.2.2.1 m).1.1.sublist ((List.take_sublist _ _).map _))
    (fun _ _ hq hqid => hX.object_thread_take_mem_iff hi hrid hq hqid)

end
end PTX
