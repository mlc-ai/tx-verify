-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStoreSites
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedule
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaBase
public import Lemmas.Flow.BulkCount
public import Lemmas.Flow.CountFirst
public import Lemmas.Flow.CountTake
public import Lemmas.Tensor.BoxWrite

@[expose] public section

/-! # The store warp's tensor stores: `StoreFacts.spec` and `OutputFacts.store_tma`

A tensor store fires at a TMA site `tma st hh` of item `n` of a thread of warp 13
(`Facts.store_tma_origin`), with the specification of that half of that stage of that item.
There the store warp's counts (`Store.Counts`) give: one more successful poll of the stage's
staged barrier than free arrivals of the stage, `n` of them; `n` earlier
stores at the instruction (`Counts.tmas`; every earlier event at a TMA position is a store,
`pc_store`); and `2 n + st` earlier commits. Its source bytes are in the stage's buffer
(`readLoc_stage`). A later free arrival of the stage or the exit comes after the stage's free
arrival of item `n` (the `n`-th one, `nth_countP`), which the bulk wait leaving `1 - st` groups
reading precedes (`Counts.lastWait`); that wait follows `2 n + 2` commits, so it observes the
store (`observes_of_commits`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### The source bytes -/

theorem mapO_box (P : Params) :
    TensorTile.count (FlashAttn4Fwd.mapO P.oBase P.sq P.h P.b P.oFill P.oClass).box 0 = 64 ∧
      TensorTile.rows (FlashAttn4Fwd.mapO P.oBase P.sq P.h P.b P.oFill P.oClass).box = 128 ∧
      (FlashAttn4Fwd.mapO P.oBase P.sq P.h P.b P.oFill P.oClass).format = .f16 ∧
      (FlashAttn4Fwd.mapO P.oBase P.sq P.h P.b P.oFill P.oClass).swizzle = .b128 := by
  simp [FlashAttn4Fwd.mapO, FlashAttn4Fwd.encodeTiled, TensorTile.count, TensorTile.step,
    TensorTile.rows, TensorTile.rowsOf]

/-- **The source bytes of a TMA store** are in its stage's buffer of the thread's CTA. -/
theorem readLoc_stage {g j st hh x y k : Nat} {l : Loc} (hhh : hh < 2)
    (h : TensorStore.readLoc (oSpec P L g j st hh) x y k = some l) :
    InStage L (ctaOf L g) st l := by
  have hw : TensorStore.readLoc (oSpec P L g j st hh) x y k =
      TensorCopy.writeLoc ⟨(oSpec P L g j st hh).toTensorBox, ⟨.shared, 0, 0⟩, true, .one⟩
        x y k := rfl
  rw [hw] at h
  obtain ⟨h0, hR, hfm, hsw⟩ := mapO_box P
  obtain ⟨hx, hy, hb⟩ := TensorCopy.writeLoc_bounds h
  have hx' : x < 64 := by rw [← h0]; exact hx
  have hy' : y < 128 := by rw [← hR]; exact hy
  have hb' : k < 2 := by
    have : TensorDescriptor.Format.bytes .f16 = 2 := rfl
    rw [← this, ← hfm]; exact hb
  rw [TensorCopy.box_writeLoc h0 hR hfm hsw hx' hy' hb'] at h
  have hoff := TensorCopy.box_offset_lt (base := stageBase L st hh) (R := 128) hx' hy' hb'
  simp only [Option.some.injEq] at h
  rw [← h]
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> simp only [oSpec, stageBase] at hoff ⊢ <;> omega

/-! ### Events at the TMA positions are stores -/

theorem pc_store_of (hX : Consistent L kernel asms mem0 X) {g j k : Nat} {x e : Event}
    {st hh : Fin 2} (hx : X.get (g, j) = some x) (he : X.get (g, k) = some e) (hjk : j < k)
    (hpc : x.pc = (Store.Site.tma st hh).pc) : Store.isStore x = true := by
  have hend := Cross.not_ends_of_lt hX hx he hjk
  rcases get_source hX hx with ⟨f, hf⟩ | ⟨t, ins, o, -, hc, hf⟩
  · exact absurd (.inl ⟨f, hf⟩) hend
  rw [hpc] at hc hf
  have hk : ∀ op, ins.op = op → ((∃ a s, x.kind = .tensorStore a s) ∨ ∃ f, x.kind = .ub f) →
      Store.isStore x = true := by
    intro op _ h
    rcases h with ⟨a, s, h⟩ | ⟨f, h⟩
    · simp [Store.isStore, h]
    · exact absurd (.inl ⟨f, h⟩) hend
  rcases Store.fin2_cases st with rfl | rfl <;> rcases Store.fin2_cases hh with rfl | rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_10)
    exact hk _ rfl (fires_cpTensorStore_kind hf)
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_11)
    exact hk _ rfl (fires_cpTensorStore_kind hf)
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_12)
    exact hk _ rfl (fires_cpTensorStore_kind hf)
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_13)
    exact hk _ rfl (fires_cpTensorStore_kind hf)

/-- Before an event of the thread, the events at a TMA position are its stores. -/
theorem pc_count (hX : Consistent L kernel asms mem0 X) {g k : Nat} {e : Event} {st hh : Fin 2}
    (he : X.get (g, k) = some e) :
    ((X.tr g).take k).countP (·.pc == (Store.Site.tma st hh).pc) =
      ((X.tr g).take k).countP
        (fun x => x.pc == (Store.Site.tma st hh).pc && Store.isStore x) := by
  apply List.countP_congr
  intro x hx
  obtain ⟨j, hj', hget⟩ := get_of_mem_take hx
  constructor
  · intro h
    simp only [beq_iff_eq] at h
    simp [h, pc_store_of hX hget he hj' h]
  · intro h
    simp only [Bool.and_eq_true] at h
    exact h.1

/-! ### The free arrivals and the exit of a store lane -/

theorem Facts.store_free_state (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g f pc tx cnt st : Nat} {rel : Bool} {sc : MbarScope}
    (hg : g < L.threads) (hw : warpOf L g = 13) (hst : st < 2)
    (he : X.get (g, f) = some ⟨pc, .arrive (freeBar L (ctaOf L g) st) tx cnt rel sc⟩) :
    ∃ n, Frame.stateAt (code L) X g f =
        some (some (.inr (.store ⟨.free ⟨st, hst⟩, n⟩))) ∧
      Store.Counts L g ⟨.free ⟨st, hst⟩, n⟩ ((X.tr g).take f) := by
  obtain ⟨⟨site, n⟩, hσ, hJ, -, hev, -⟩ := Facts.store_ev' hpre hX ht hg hw he id nofun
  obtain ⟨st0, rfl, hm, -⟩ := Store.ev_arrive hev
  obtain ⟨-, h0⟩ := Store.freeAt_inj hm
  obtain rfl : st0 = ⟨st, hst⟩ := Fin.ext h0.symm
  exact ⟨n, hσ, hJ⟩

theorem Facts.store_exit_state (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g e pc : Nat} (hg : g < L.threads) (hw : warpOf L g = 13)
    (he : X.get (g, e) = some ⟨pc, .exit⟩) :
    ∃ n, Store.Counts L g ⟨.exit, n⟩ ((X.tr g).take e) := by
  obtain ⟨⟨site, n⟩, -, hJ, -, hev, -⟩ := Facts.store_ev' hpre hX ht hg hw he id nofun
  cases site <;> simp only [Store.Ev, reduceCtorEq, exists_false] at hev
  exact ⟨n, hJ⟩

/-! ### The store's source and its bulk wait -/

theorem commits_eq (es : List Event) : Flow.commits es = es.countP Store.isCommit := by
  unfold Flow.commits
  apply List.countP_congr
  intro x _
  rfl

/-- **A tensor store's source**: its stage's buffer, its polls, arrivals and earlier executions,
and the bulk wait that later free arrivals and the exit follow. -/
theorem Facts.store_src (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k pc a : Nat} {s : TensorStore.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorStore a s⟩) :
    ∃ st hh : Fin 2, warpOf L g = 13 ∧ StoreSrc L X g k pc s st ∧
      pc = Store.Site.pc (.tma st hh) ∧ a = P.oMap ∧
      workOf L g (arrivals (freeBar L (ctaOf L g) st) ((X.tr g).take k)) < totOf L ∧
      s = oSpec P L g (arrivals (freeBar L (ctaOf L g) st) ((X.tr g).take k)) st hh := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨hw, st, hh, n, -, hJ, hn, hpc, ha, hs⟩ := Facts.store_tma_origin hpre hX ht he
  have hst : st.val < 2 := st.isLt
  have hfr : arrivals (freeBar L (ctaOf L g) st) ((X.tr g).take k) = n := by
    have := hJ.freed st
    rw [Store.freeAt_eq] at this
    rw [this]
    rcases Store.fin2_cases st with rfl | rfl <;> rcases Store.fin2_cases hh with rfl | rfl <;>
      simp [Store.done, Store.before, Store.Site.pos]
  have hsg : okPolls (stagedBar L (ctaOf L g) st) ((X.tr g).take k) = n + 1 := by
    have := hJ.staged st
    rw [Store.stagedAt_eq] at this
    rw [this]
    rcases Store.fin2_cases st with rfl | rfl <;> rcases Store.fin2_cases hh with rfl | rfl <;>
      simp [Store.done, Store.before, Store.Site.pos]
  have hcm : Flow.commits ((X.tr g).take k) = 2 * n + st.val := by
    rw [commits_eq, hJ.commits]
    rcases Store.fin2_cases st with rfl | rfl <;> rcases Store.fin2_cases hh with rfl | rfl <;>
      simp [Store.done, Store.before, Store.Site.pos]
  have htm : ((X.tr g).take k).countP (·.pc == pc) = n := by
    rw [hpc, pc_count hX he, hJ.tmas st hh]
    rcases Store.fin2_cases st with rfl | rfl <;> rcases Store.fin2_cases hh with rfl | rfl <;>
      simp [Store.done, Store.before, Store.Site.pos]
  refine ⟨st, hh, hw, ⟨by rw [hs]; rfl, fun x y z l hl => ?_, by rw [hsg, hfr], by rw [htm, hfr],
    ?_⟩, hpc, ha, by rw [hfr]; exact Work.workOf_lt hpre hn, by rw [hfr]; exact hs⟩
  · rw [hs] at hl
    exact readLoc_stage hh.isLt hl
  · intro e pce hke hev
    have hk := (List.getElem?_eq_some_iff.mp he).1
    -- The stage's free arrival of item `n` is before `e`.
    have hmore : ∃ K, K ≤ e + 1 ∧
        n < ((X.tr g).take K).countP (arrivesOn (freeBar L (ctaOf L g) st)) := by
      rcases hev with hx | ⟨tx, cnt, rel, sc, hx⟩
      · obtain ⟨m, hJe⟩ := Facts.store_exit_state hpre hX ht hg hw hx
        have := hJe.freed st
        rw [Store.freeAt_eq] at this
        refine ⟨e, by omega, ?_⟩
        show n < arrivals _ _
        rw [this]
        simp only [Store.done, ↓reduceIte, Store.before, Store.Site.pos]
        rcases Store.fin2_cases st with rfl | rfl <;> simp <;> omega
      · refine ⟨e + 1, le_refl _, ?_⟩
        have he' : (X.tr g)[e]? = some _ := hx
        rw [List.take_add_one, he', Option.toList_some, List.countP_append]
        have hmono := (List.take_sublist_take_left (l := X.tr g)
          (show k ≤ e by omega)).countP_le (p := arrivesOn (freeBar L (ctaOf L g) st))
        have h1 : arrivesOn (freeBar L (ctaOf L g) st)
            ⟨pce, .arrive (freeBar L (ctaOf L g) st) tx cnt rel sc⟩ = true :=
          arrivesOn_arrive rfl |>.trans (by simp)
        unfold arrivals at hfr
        simp only [List.countP_singleton, h1, ↓reduceIte]
        omega
    obtain ⟨K, hK, hlt⟩ := hmore
    obtain ⟨f, hfK, x, hx, hxa, hcf⟩ := nth_countP hlt
    have hfx : X.get (g, f) = some x := hx
    -- `f` is after the store.
    have hkf : k < f := by
      by_contra hle
      rcases Nat.lt_or_ge f k with hlt' | hge
      · have := (List.take_sublist_take_left (l := X.tr g)
          (show f + 1 ≤ k by omega)).countP_le (p := arrivesOn (freeBar L (ctaOf L g) st))
        rw [List.take_add_one, hx, Option.toList_some, List.countP_append, hcf] at this
        unfold arrivals at hfr
        simp only [List.countP_singleton, hxa, ↓reduceIte] at this
        omega
      · have hfk : f = k := by omega
        subst hfk
        rw [he] at hfx
        obtain rfl := Option.some.inj hfx
        simp [arrivesOn, sourceArrive] at hxa
    obtain ⟨xtx, xc, xrel, xsc, hxk⟩ := arrivesOn_form hxa
    have hfa : X.get (g, f) = some ⟨x.pc, .arrive (freeBar L (ctaOf L g) st) xtx xc xrel xsc⟩ := by
      rw [hfx]
      obtain ⟨xpc, xk⟩ := x
      simp only at hxk ⊢
      rw [hxk]
    obtain ⟨n', hσf, hJf⟩ := Facts.store_free_state hpre hX ht hg hw hst hfa
    have hn' : n' = n := by
      have := hJf.freed ⟨st, hst⟩
      rw [Store.freeAt_eq] at this
      unfold arrivals at this
      rw [hcf] at this
      have hb : Store.before (.free ⟨st, hst⟩) ⟨.free ⟨st, hst⟩, n'⟩ = 0 := by
        simp [Store.before]
      simp only [Store.done, hb] at this
      simp at this
      omega
    subst n'
    obtain ⟨wpc, hlast⟩ := hJf.lastWait ⟨st, hst⟩ rfl
    have hfl : f ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp hfx).1.le
    obtain ⟨w, hfw, hwget⟩ := getLast_take hlast hfl
    subst hfw
    have hkw : k < w := by
      rcases Nat.lt_or_ge k w with h | h
      · exact h
      · have : w = k := by omega
        subst this
        rw [he] at hwget
        cases hwget
    have harr : arrivals (freeBar L (ctaOf L g) st) ((X.tr g).take w) = n := by
      have h1 := countP_take_succ_false (p := arrivesOn (freeBar L (ctaOf L g) st)) hwget
        (by simp [arrivesOn, sourceArrive])
      unfold arrivals
      rw [← h1, hcf]
    have hcw : Flow.commits ((X.tr g).take w) = 2 * n + 2 := by
      have h1 := countP_take_succ_false (p := Store.isCommit) hwget (by simp [Store.isCommit])
      rw [commits_eq, ← h1, hJf.commits]
      rcases Store.fin2_cases (⟨st, hst⟩ : Fin 2) with h | h <;> rw [h] <;>
        simp [Store.done, Store.before, Store.Site.pos]
    refine ⟨w, hkw, by omega, ⟨wpc, _, hwget, observes_of_commits he hkw ?_⟩, by rw [harr, hfr]⟩
    rw [hcm, hcw]
    have : st.val = 0 ∨ st.val = 1 := by omega
    rcases this with h | h <;> simp [h]

/-- **`StoreFacts.spec`**: every tensor store is a store lane's store of a half of a stage of
the item numbered by its free arrivals of the stage. -/
theorem StoreFacts_spec (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) :
    ∀ {g k pc a : Nat} {s : TensorStore.Spec}, g < L.threads →
      X.get (g, k) = some ⟨pc, .tensorStore a s⟩ →
        ∃ st hh : Fin 2, warpOf L g = 13 ∧ StoreSrc L X g k pc s st ∧
          pc = Store.Site.pc (.tma st hh) ∧ a = P.oMap ∧
          workOf L g (arrivals (freeBar L (ctaOf L g) st) ((X.tr g).take k)) < totOf L ∧
          s = oSpec P L g (arrivals (freeBar L (ctaOf L g) st) ((X.tr g).take k)) st hh :=
  fun _ he => Facts.store_src hpre hX ht he

/-- **`OutputFacts.store_tma`**: every tensor store is a store lane's, of a stage. -/
theorem OutputFacts_store_tma (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) :
    ∀ {g i pc addr : Nat} {s : TensorStore.Spec}, g < L.threads →
      X.get (g, i) = some ⟨pc, .tensorStore addr s⟩ →
        warpOf L g = 13 ∧ ∃ st < 2, StoreSrc L X g i pc s st := by
  intro g i pc addr s _ he
  obtain ⟨st, hh, hw, hsrc, -⟩ := Facts.store_src hpre hX ht he
  exact ⟨hw, st.val, st.isLt, hsrc⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof
