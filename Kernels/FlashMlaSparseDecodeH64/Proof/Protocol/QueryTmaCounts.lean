-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryTmaRecords
public import Lemmas.MBarrier.MBarrierTransactions
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.QueryTmaSites
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1MmaLeader
import Lemmas.Protocol.MbarInit

public section

/-! # The query object's unique arrival and eight distinct completions -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryTmaRecords

open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {cta : Nat}

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X) (hs : Sound P L)
include hpre hX hs

/-- Every record charging the query object names the same elected lane's single expect-tx node. -/
theorem arrival_node_eq (ht : Frame.Tracked (Machine.code P L) X) {r q : Record Ref}
    {n tx n' tx' : Nat} (hr : r ∈ X.objects (object L cta)) (hq : q ∈ X.objects (object L cta))
    (ha : r.action = .arrive n tx) (hb : q.action = .arrive n' tx') : r.id = q.id := by
  obtain ⟨_, _, g, i, e, d, hId, he, hCta, hState, hSite⟩ :=
    arrival_record hpre hX hs ht hr ha
  obtain ⟨_, _, w, j, f, d', hId', hf, hCta', hState', hSite'⟩ :=
    arrival_record hpre hX hs ht hq hb
  obtain ⟨_, hLeader⟩ := Wg1MmaLeader.cta_issuer (cta := cta) hpre hX hs
  have hG := (hLeader g i d hCta hState (by simp [hSite])).trans
    (hLeader w j d' hCta' hState' (by simp [hSite'])).symm
  subst w
  have hJ := QueryTmaSites.arrive_site_unique he hf hState hState' hSite hSite'
  rw [hId, hId', hJ]

/-- Thus the checked query history has at most one expect-tx record, faulting or otherwise. -/
theorem arrival_record_eq (ht : Frame.Tracked (Machine.code P L) X) {r q : Record Ref}
    {n tx n' tx' : Nat} (hr : r ∈ X.objects (object L cta)) (hq : q ∈ X.objects (object L cta))
    (ha : r.action = .arrive n tx) (hb : q.action = .arrive n' tx') : r = q := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hq
  have hId := arrival_node_eq hpre hX hs ht hr hq ha hb
  obtain rfl := ObjectInit.checked_record_index_eq (hX.tma.2.2.1 (object L cta)).1 hi hj hId
  exact Option.some.inj (hi.symm.trans hj)

omit hpre hX hs in
private def completing (r : Record Ref) : Bool :=
  match r.action, r.fault with
  | .completeTx _, none => true
  | _, _ => false

omit hpre hX hs in
private theorem completing_action {r : Record Ref} (hr : completing r = true) :
    ∃ n, r.action = .completeTx n := by
  unfold completing at hr
  split at hr
  · exact ⟨_, by assumption⟩
  · cases hr

/-- The eight query tiles bound the actual successful completion records, also in any prefix. -/
theorem completed_count_le (ht : Frame.Tracked (Machine.code P L) X) (k : Nat) :
    completedTxCount ((X.objects (object L cta)).take k) ≤ 8 := by
  classical
  let log := X.objects (object L cta)
  let ids := (((log.take k).filter completing).map Record.id).toFinset
  have hSource (x : Ref) (hx : x ∈ ids) :
      ∃ g i e q tile, x = .async (g, i) (.notify .load) ∧
        X.get (g, i) = some e ∧ ctaOf L g = cta ∧
        Frame.stateAt (Machine.code P L) X g i = some (some (.mma q)) ∧ q.site = .qLoad tile := by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    obtain ⟨hTake, hComp⟩ := List.mem_filter.mp hr
    obtain ⟨n, ha⟩ := completing_action hComp
    obtain ⟨_, g, i, e, a, sp, q, tile, hid, he, hk, hc, hstate, hsite, hspec⟩ :=
      completion_source hpre hX hs ht (List.mem_of_mem_take hTake) ha
    exact ⟨g, i, e, q, tile, hid, he, hc, hstate, hsite⟩
  have hTile (x : Ref) (hx : x ∈ ids) :
      ∃ tile : Fin 8, ∃ g i e q, x = .async (g, i) (.notify .load) ∧
        X.get (g, i) = some e ∧ ctaOf L g = cta ∧
        Frame.stateAt (Machine.code P L) X g i = some (some (.mma q)) ∧ q.site = .qLoad tile := by
    obtain ⟨g, i, e, q, tile, h⟩ := hSource x hx
    exact ⟨tile, g, i, e, q, h⟩
  let tileOf (x : Ref) : Fin 8 := if hx : x ∈ ids then (hTile x hx).choose else 0
  have hMember {x : Ref} (hx : x ∈ ids) :
      ∃ g i e q, x = .async (g, i) (.notify .load) ∧ X.get (g, i) = some e ∧
        ctaOf L g = cta ∧ Frame.stateAt (Machine.code P L) X g i = some (some (.mma q)) ∧
        q.site = .qLoad (tileOf x) := by
    rw [show tileOf x = (hTile x hx).choose by simp [tileOf, hx]]
    exact (hTile x hx).choose_spec
  have hinj : Set.InjOn tileOf (↑ids : Set Ref) := by
    intro x hx y hy hEq
    obtain ⟨g, i, e, d, rfl, he, hc, hState, hSite⟩ := hMember hx
    obtain ⟨w, j, f, d', rfl, hf, hc', hState', hSite'⟩ := hMember hy
    rw [← hEq] at hSite'
    obtain ⟨_, hLeader⟩ := Wg1MmaLeader.cta_issuer (cta := cta) hpre hX hs
    have hGw := (hLeader g i d hc hState (by simp [hSite])).trans
      (hLeader w j d' hc' hState' (by simp [hSite'])).symm
    subst w
    have := QueryTmaSites.load_site_unique he hf hState hState' hSite hSite'
    cases this
    rfl
  have hLe := Finset.card_le_card_of_injOn (t := Finset.univ) tileOf
    (fun _ _ => Finset.mem_univ _) hinj
  have hNd := ((hX.tma.2.2.1 (object L cta)).1.1.sublist
    ((List.take_sublist k log).map Record.id)).sublist
      ((List.filter_sublist (p := completing) (l := log.take k)).map Record.id)
  rw [show completedTxCount (log.take k) = (log.take k).countP completing from rfl,
    List.countP_eq_length_filter, ← List.length_map Record.id, ← List.toFinset_card_of_nodup hNd]
  exact hLe

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryTmaRecords
