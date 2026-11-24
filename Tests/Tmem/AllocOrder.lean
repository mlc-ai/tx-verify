-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.Order
public import Lemmas.Order.OrderNotAccess

/-!
# The address store of `tcgen05.alloc` is an ordinary generic-proxy write (§9.7.18.7.1)

§9.7.18.7.1, Example 1:

``` tcgen05.alloc.cta_group::1.sync.aligned.shared::cta.b32 [sMemAddr1], 32; ld.shared.b32 taddr,
[sMemAddr1]; ```

Lanes 0 and 1 of warp 0 execute the allocation; lane 0 then stores the address
(EXT-TCALLOC-STORER) as a weak write after its alloc event. The result is ordered before a
participating lane's ordinary load of the word at the four result bytes.

`X m v src` is the execution of lanes 0 and 1 in three shapes, lane 1's load returning `v` from
the sources `src`:
* `m = 0`: lane 1 reads the result without a separate barrier. The load is ordered
  with the store and cannot read the launch content (`example1_no_race`, `example1_w0_rejected`).
* `m = 1`: both lanes meet at `bar.warp.sync` between the store and the load. The store
  happens before the load, the execution has no `Race`, and `Hidden` makes the load read the
  stored bytes (`warpbar_baseCausality`, `warpbar_no_race`, `warpbar_source`,
  `warpbar_reads_store`).
* `m = 2`: lane 0 loads its own store back. They are ordered by program order and do not race
  (`self_no_race`). -/
namespace PTX.Tests.AllocOrder
noncomputable section

def L : Launch := { grid := 1, block := 64, params := fun _ => none }

def dst : Loc := ⟨.shared, 0, 0⟩
def acc : Acc := { loc := dst, size := 4 }
def b : Byte := (.bits 8 0, 0)
def word : List (Option Byte) := [some b, some b, some b, some b]

def allocEv : Event := ⟨0, .tc (.resource .one (some dst) (.alloc 32))⟩
def storeEv : Event := ⟨0, .wr acc [b, b, b, b]⟩
def barEv : Event := ⟨1, .warpBar 0xffffffff 0⟩
def loadEv (v : List (Option Byte)) : Event := ⟨2, .rd acc v⟩

/-- Lane 0: alloc, store (then `bar.warp.sync` for `m = 1`, a load for `m = 2`). Lane 1 (not for
`m = 2`): alloc, (`bar.warp.sync` for `m = 1`,) load. -/
def X (m : Nat) (v : List (Option Byte)) (src : Nat → Option AsyncCopy.Ref) : Execution where
  tr g :=
    if g = 0 then
      (if m = 1 then [allocEv, storeEv, barEv] else if m = 2 then [allocEv, storeEv, loadEv v]
        else [allocEv, storeEv])
    else if g = 1 then
      (if m = 0 then [allocEv, loadEv v] else if m = 1 then [allocEv, barEv, loadEv v] else [])
    else []
  rf e k := if e = .thread (1, 2) ∨ e = .thread (1, 1) ∨ e = .thread (0, 2) then src k else none

/-- The events of `X m v src` are an alloc, the store, the load and (for `m = 1`) the barrier,
at fixed places. -/
theorem get_cases {m : Nat} {v src} {e : EvId} {ev : Event} (h : (X m v src).get e = some ev) :
    ev = allocEv ∨ (e = (0, 1) ∧ ev = storeEv) ∨ (m = 1 ∧ ev = barEv) ∨
      (ev = loadEv v ∧ ((m = 0 ∧ e = (1, 1)) ∨ (m = 1 ∧ e = (1, 2)) ∨ (m = 2 ∧ e = (0, 2)))) := by
  obtain ⟨g, k⟩ := e
  simp only [Execution.get, X] at h
  split_ifs at h with h0 h1 h2 h3 h4 h5 <;> subst_vars <;>
    rcases k with _ | _ | _ | k <;> simp_all

theorem get_kind {m : Nat} {v src} {e : EvId} {pc : Nat} {k : Kind}
    (h : (X m v src).get e = some ⟨pc, k⟩) :
    k = allocEv.kind ∨ k = storeEv.kind ∨ k = barEv.kind ∨ k = (loadEv v).kind := by
  rcases get_cases h with h | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · exact .inl (congrArg Event.kind h)
  · exact .inr (.inl (congrArg Event.kind h))
  · exact .inr (.inr (.inl (congrArg Event.kind h)))
  · exact .inr (.inr (.inr (congrArg Event.kind h)))

/-- Memory operations of `X m v src`: the store (a write) and the load (a read), both of `acc`. -/
theorem intent_cases {m : Nat} {v src} {r : AsyncCopy.Ref} {c : Acc} {w : Bool}
    (h : (X m v src).Intent r c w) :
    ∃ i, r = .thread i ∧ c = acc ∧ ((w = true ∧ i = (0, 1)) ∨
      (w = false ∧ ((m = 0 ∧ i = (1, 1)) ∨ (m = 1 ∧ i = (1, 2)) ∨ (m = 2 ∧ i = (0, 2))))) := by
  have nk : ∀ {i pc k}, (X m v src).get i = some ⟨pc, k⟩ →
      k = allocEv.kind ∨ k = storeEv.kind ∨ k = barEv.kind ∨ k = (loadEv v).kind := get_kind
  have nt : ∀ i a s, ¬ (X m v src).TensorIssue i a s := by
    rintro i a s ⟨pc, hp⟩; rcases nk hp with h | h | h | h <;> cases h
  have ns : ∀ i a s, ¬ (X m v src).TensorStoreIssue i a s := by
    rintro i a s ⟨pc, hp⟩; rcases nk hp with h | h | h | h <;> cases h
  have nc : ∀ i s ts, ¬ (X m v src).ClcIssue i s ts := by
    rintro i s ts ⟨pc, hp⟩; rcases nk hp with h | h | h | h <;> cases h
  have nb : ∀ i s, ¬ (X m v src).Copy i s := by
    rintro i s ⟨pc, hp⟩; rcases nk hp with h | h | h | h <;> cases h
  have nm : ∀ i d s acc mask, ¬ (X m v src).MmaIssue i d s acc mask := by
    rintro i d s acc mask ⟨pc, hp⟩; rcases nk hp with h | h | h | h <;> cases h
  have ncp : ∀ i c, ¬ (X m v src).CpIssue i c := by
    rintro i c ⟨pc, hp⟩; rcases nk hp with h | h | h | h <;> cases h
  have npf : ∀ i a s, ¬ (X m v src).TensorPrefetchIssue i a s := by
    rintro i a s ⟨pc, hp⟩; rcases nk hp with h | h | h | h <;> cases h
  have nbp : ∀ i a, ¬ (X m v src).BulkPrefetch i a := by
    rintro i a ⟨pc, hp⟩; rcases nk hp with h | h | h | h <;> cases h
  cases r with
  | async i p =>
    exfalso
    cases p <;> simp [Execution.Intent, AsyncCopy.Part.writes, Execution.AsyncFootprint, and_false,
      Execution.MmaFootprint, nt, ns, nc, nb, nm, ncp, npf, nbp] at h
  | thread i =>
    refine ⟨i, rfl, ?_⟩
    rcases h with ⟨bs, ⟨pc, hp⟩, rfl⟩ | ⟨bs, ⟨pc, hp⟩, rfl⟩ | ⟨old, new, pc, hp⟩ <;>
      rcases get_cases hp with h | ⟨rfl, h⟩ | ⟨-, h⟩ | ⟨h, hi⟩ <;>
      simp_all [allocEv, storeEv, barEv, loadEv]

/-- No synchronization in `m = 0` or `m = 2`: causality is program order. -/
theorem baseCausality_po {m : Nat} (hm : m ≠ 1) {v src} {e f : EvId}
    (h : baseCausality L (X m v src) e f) :
    po (X m v src) e f := by
  have nk : ∀ {i pc k}, (X m v src).get i = some ⟨pc, k⟩ →
      k = allocEv.kind ∨ k = storeEv.kind ∨ k = (loadEv v).kind := by
    intro i pc k hp
    rcases get_cases hp with h | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp_all [allocEv, storeEv, loadEv]
  refine baseCausality_of_noBar ?_ ?_ ?_ ?_ ?_ ?_ h
  · rintro e k ⟨-, ⟨count, pc, hp⟩, -⟩
    rcases nk hp with h | h | h <;> cases h
  · rintro w n ⟨pc, q, sc, hp⟩
    rcases nk hp with h | h | h <;> cases h
  · rintro e f ⟨-, i, j, ⟨phase, ⟨k, s, t, cta, w, lanes, g, hi, -⟩, -⟩, -⟩
    simp [X] at hi
  · rintro e f ⟨i, j, ⟨-, mask, inst, ⟨pc, hp⟩, -⟩, -⟩
    rcases nk hp with h | h | h <;> cases h
  · rintro e f ⟨a, b, bs, cs, hw, -, hrel, -⟩
    rcases hw with ⟨pc, hp⟩ | ⟨old, ⟨pc, hp⟩⟩
    · rcases get_cases hp with h | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
        simp_all [allocEv, storeEv, loadEv]
      simp [acc] at hrel
    · rcases nk hp with h | h | h <;> cases h
  · rintro e f (⟨w, r, a, b, bs, cs, se, sf, -, -, -, -, -, hf, -⟩ | ⟨-, hsc⟩)
    · rcases hf with ⟨sem, sc, ⟨pc, hp⟩ | ⟨pc, hp⟩⟩ <;> (rcases nk hp with h | h | h <;> cases h)
    · simp [X] at hsc

/-- The two lanes have no cross-lane base-causality edge without a barrier. -/
theorem bare_no_baseCausality {v src} : ¬ baseCausality L (X 0 v src) (0, 1) (1, 1) :=
  fun h => (by decide : (0 : Nat) ≠ 1) (baseCausality_po (by decide) h).1

/-- The allocation publishes the result at each byte loaded by lane 1. -/
theorem bare_result_order {v src} {l : Loc} (hc : acc.Covers l) :
    modelCausality L (X 0 v src) l (.thread (0, 1)) (.thread (1, 1)) := by
  apply modelCausality.of_allocResultBefore
  refine ⟨0, dst, acc, v, ?_, by decide, hc, ⟨2, rfl⟩, hc⟩
  refine ⟨?_, rfl, rfl, rfl, 0, 0, .one, 32, 0, [b, b, b, b], rfl, rfl, rfl,
    ⟨⟨allocEv, rfl, rfl⟩, rfl⟩, ⟨⟨allocEv, rfl, rfl⟩, rfl⟩, rfl⟩
  simp [SameWarp, SameCta, L, Launch.threads]

/-- If the store is ordered before the load, the execution has no `Race`. -/
theorem no_race_of {m : Nat} {v src}
    (hh : ∀ i l, ((m = 0 ∧ i = (1, 1)) ∨ (m = 1 ∧ i = (1, 2)) ∨
      (m = 2 ∧ i = (0, 2))) → acc.Covers l →
      modelCausality L (X m v src) l (.thread (0, 1)) (.thread i)) :
    ¬ Race L (X m v src) := by
  rintro ⟨e, f, a, a', l, ⟨hne, we, wf, he, hf, hw, -⟩, -, hc, -, hef, hfe, -⟩
  obtain ⟨i, rfl, rfl, hi⟩ := intent_cases he
  obtain ⟨j, rfl, rfl, hj⟩ := intent_cases hf
  rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, hi⟩ <;> rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, hj⟩
  · exact hne rfl
  · exact hef (.direct (hh j l hj hc))
  · exact hfe (.direct (hh i l hi hc))
  · simp at hw

/-- The immediate result load in PTX Example 1 does not race with the allocation store. -/
theorem example1_no_race {v src} : ¬ Race L (X 0 v src) := by
  apply no_race_of
  rintro i l (⟨-, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩) hc
  · exact bare_result_order hc
  · cases h
  · cases h

/-- The read-back value cannot come from the launch content, even without a barrier. -/
theorem example1_w0_rejected {v} : ¬ Hidden L (X 0 v (fun _ => none)) := by
  intro hh
  exact hh (.thread (1, 1)) acc v 0 (.thread (0, 1)) acc [b, b, b, b]
    (.inl ⟨2, rfl⟩) (by decide) (.inl ⟨0, rfl⟩) (Acc.covers_at (by decide))
    (.direct (bare_result_order (Acc.covers_at (by decide))))

/-- With `bar.warp.sync` between them, lane 0's store happens before lane 1's load. -/
theorem warpbar_baseCausality {v src} : baseCausality L (X 1 v src) (0, 1) (1, 2) := by
  refine .single (.inr (.inr (.inr (.inr (.inl ?_)))))
  refine ⟨2, 1, ⟨?_, 0xffffffff, 0, ⟨1, ?_⟩, ⟨1, ?_⟩⟩, by decide, by decide, ?_⟩
  · simp [SameWarp, SameCta, L, Launch.threads]
  · simp [Execution.get, X, barEv]
  · simp [Execution.get, X, barEv]
  · simp [X]

/-- **Example 1 with `bar.warp.sync` has no race.** -/
theorem warpbar_no_race {v src} : ¬ Race L (X 1 v src) := by
  apply no_race_of
  rintro i l (⟨h, -⟩ | ⟨-, rfl⟩ | ⟨h, -⟩) _
  · cases h
  · exact .inl warpbar_baseCausality
  · cases h

/-- **A lane reading back its own store does not race**: the two are ordered by program order. -/
theorem self_no_race {v src} : ¬ Race L (X 2 v src) := by
  apply no_race_of
  rintro i l (⟨h, -⟩ | ⟨h, -⟩ | ⟨-, rfl⟩) _
  · cases h
  · cases h
  · exact .inl (.single (.inl ⟨rfl, by decide, by simp [X], fun h => by
      have := h.2 1 le_rfl
      simp [Execution.get, X, loadEv, storeEv, Event.acc, Acc.shift, acc, dst] at this⟩))

/-- Given `Hidden`, each byte of the load after `bar.warp.sync` has a source that is a write
(not `W0`) not visible before the store. -/
theorem warpbar_source {v src} (hh : Hidden L (X 1 v src)) :
    ∀ k < 4, match (X 1 v src).rf (.thread (1, 2)) k with
      | none => False
      | some w => ¬ ByteCausality L (X 1 v src) (acc.loc.at k) w (.thread (0, 1)) :=
  fun k hk => hh (.thread (1, 2)) acc v k (.thread (0, 1)) acc [b, b, b, b] (.inl ⟨2, rfl⟩) hk
    (.inl ⟨0, rfl⟩)
    (Acc.covers_at hk) (.direct (.inl warpbar_baseCausality))

/-- The only write of the execution is lane 0's address store. -/
theorem writes_cases {m : Nat} {v src} {w : AsyncCopy.Ref} {a : Acc} {bs : List Byte}
    (h : (X m v src).MemWrites w a bs) : w = .thread (0, 1) ∧ a = acc ∧ bs = [b, b, b, b] := by
  have nk : ∀ {i pc k}, (X m v src).get i = some ⟨pc, k⟩ →
      k = allocEv.kind ∨ k = storeEv.kind ∨ k = barEv.kind ∨ k = (loadEv v).kind := get_kind
  cases w with
  | thread i =>
    obtain ⟨pc, hp⟩ | ⟨old, hp⟩ := h
    · rcases get_cases hp with h | ⟨rfl, h⟩ | ⟨-, h⟩ | ⟨h, -⟩ <;>
        simp_all [allocEv, storeEv, barEv, loadEv]
    · obtain ⟨pc, hp⟩ := hp
      rcases nk hp with h | h | h | h <;> cases h
  | async i p =>
    exfalso
    have nb : ∀ i s, ¬ (X m v src).Copy i s := by
      rintro i s ⟨pc, hp⟩; rcases nk hp with h | h | h | h <;> cases h
    have nc : ∀ i s ts, ¬ (X m v src).ClcIssue i s ts := by
      rintro i s ts ⟨pc, hp⟩; rcases nk hp with h | h | h | h <;> cases h
    cases p
    case writeCopy =>
      obtain ⟨_, hb, _⟩ := h
      exact nb _ _ hb
    case writeCta =>
      obtain ⟨_, _, hc, _⟩ := h
      exact nc _ _ _ hc
    all_goals simp [Execution.MemWrites, X] at h

/-- **The load after `bar.warp.sync` reads lane 0's bytes**: whatever its sources, `RfWf` and
`Hidden` make it return the stored address. -/
theorem warpbar_reads_store {mem0 : Mem0} {v src} (hrf : RfWf mem0 (X 1 v src))
    (hh : Hidden L (X 1 v src)) : v = word := by
  obtain ⟨hlen, hsrc⟩ := hrf (.thread (1, 2)) acc v (.inl ⟨2, rfl⟩)
  have hbyte : ∀ k < 4, v[k]? = some (some b) := by
    intro k hk
    have h := warpbar_source hh k hk
    have hs := hsrc k hk
    have hrf' : (X 1 v src).rf (.thread (1, 2)) k = src k := by simp [X]
    rw [hrf'] at h hs
    cases hk' : src k with
    | none => rw [hk'] at h; exact h.elim
    | some w =>
      rw [hk'] at hs
      obtain ⟨a', bs', hw, -, hv⟩ := hs
      obtain ⟨rfl, rfl, rfl⟩ := writes_cases hw
      rw [hv]
      simp only [wbyte, Loc.at, acc]
      match k, hk with
      | 0, _ | 1, _ | 2, _ | 3, _ => rfl
  match v, hlen, hbyte with
  | [x0, x1, x2, x3], _, hbyte =>
    have h0 := hbyte 0 (by decide)
    have h1 := hbyte 1 (by decide)
    have h2 := hbyte 2 (by decide)
    have h3 := hbyte 3 (by decide)
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h0 h1 h2 h3
    rw [h0, h1, h2, h3, word]

end
end PTX.Tests.AllocOrder
