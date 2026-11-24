-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStoreTma
public import Kernels.FlashAttn4Fwd.Proof.Safety.TensorAlloc

@[expose] public section

/-! # The store warp's tensor stores: `StoreFacts.issued` and `AsyncFacts.store_bounds`

* A store lane that exited is at its exit site with every item done, so each TMA site has fired
  one store per item (`Counts.tmas`); its `j`-th store there (`nth_countP`) has `j` earlier
  executions of the instruction, which number its free arrivals of the stage (`StoreSrc`).
* A tensor store's box is inside the O map (`oSpec_in_bounds`): its columns `64 hh + x < 128`,
  rows `512 m + 256 st + 128 r + y < 512 m + 512 ≤ seqlen_q`, and the item's head and batch below
  the map's (`Schedule.coords_lt`; `Safety.tile_in_bounds`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem Store.tma_pc_inj : ∀ st hh st' hh' : Fin 2,
    (Store.Site.tma st hh).pc = (Store.Site.tma st' hh').pc → st = st' ∧ hh = hh' := by
  decide

/-- **`StoreFacts.issued`**: a store lane that exited issued the store of every half of every
stage of every item of its cluster. -/
theorem StoreFacts_issued (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) :
    ∀ {g : Nat}, g < L.threads → warpOf L g = 13 →
      (∃ pc, (X.tr g).getLast? = some ⟨pc, .exit⟩) → ∀ j, workOf L g j < totOf L →
        ∀ st hh : Fin 2, ∃ k a s, X.get (g, k) =
            some ⟨Store.Site.pc (.tma st hh), .tensorStore a s⟩ ∧
          arrivals (freeBar L (ctaOf L g) st) ((X.tr g).take k) = j := by
  intro g hg hw ⟨pce, hlast⟩ j hj st hh
  have hjT : j < Work.T L g := by
    rw [Work.lt_T_iff hpre, ← Work.totOf_eq' hpre]
    exact hj
  have hlen : 0 < (X.tr g).length := by
    rcases h : X.tr g with _ | ⟨x, xs⟩
    · rw [h] at hlast; cases hlast
    · simp
  have hE : X.get (g, (X.tr g).length - 1) = some ⟨pce, .exit⟩ := by
    show (X.tr g)[(X.tr g).length - 1]? = _
    rw [← List.getLast?_eq_getElem?]
    exact hlast
  obtain ⟨n, hJ⟩ := Facts.store_exit_state hpre hX ht hg hw hE
  have hcnt := hJ.tmas st hh
  simp only [Store.done, ↓reduceIte, Store.before, Store.Site.pos] at hcnt
  have hlt : j < ((X.tr g).take ((X.tr g).length - 1)).countP
      (fun e => e.pc == (Store.Site.tma st hh).pc && Store.isStore e) := by
    rw [hcnt]
    rcases Store.fin2_cases st with rfl | rfl <;> rcases Store.fin2_cases hh with rfl | rfl <;>
      simp <;> omega
  obtain ⟨b, hb, x, hx, hxp, hcb⟩ := nth_countP hlt
  simp only [Bool.and_eq_true, beq_iff_eq] at hxp
  obtain ⟨hpc, hst⟩ := hxp
  obtain ⟨xpc, xk⟩ := x
  simp only at hpc
  subst hpc
  obtain ⟨a, s, hxk⟩ : ∃ a s, xk = .tensorStore a s := by
    revert hst
    cases xk <;> simp [Store.isStore]
  subst hxk
  have hxb : X.get (g, b) = some ⟨(Store.Site.tma st hh).pc, .tensorStore a s⟩ := hx
  obtain ⟨st', hh', -, hsrc, hpc', -⟩ := Facts.store_src hpre hX ht hxb
  obtain ⟨rfl, rfl⟩ := Store.tma_pc_inj _ _ _ _ hpc'
  refine ⟨b, a, s, hxb, ?_⟩
  rw [← hsrc.2.2.2.1, pc_count hX hxb]
  exact hcb

/-! ### The box of a tensor store -/

/-- **The O map's box of an item's stage half is inside the map.** -/
theorem oSpec_in_bounds (hpre : Pre P L mem0) {g j st hh : Nat} (hj : j < Work.T L g)
    (hst : st < 2) (hhh : hh < 2) :
    ¬ TensorHasOob (oSpec P L g j st hh).descriptor (oSpec P L g j st hh).origin
      (oSpec P L g j st hh).rows := by
  obtain ⟨hw, -, -, hm⟩ := Work.Dm.item_bounds hpre hj
  have hwi : workOf L g j < P.items := (Work.lt_T_iff (g := g) hpre).mp hj
  have hc := Schedule.coords_eq hpre (show workOf L g j < 2 ^ 32 by omega)
  have hl := Schedule.coords_lt hpre hwi
  have hrk := rankOf_eq hpre g
  have hhd : tileHead L g j < P.h := by
    simp only [tileHead, hc]
    exact hl.2.1
  have hbt : tileBatch L g j < P.b := by
    simp only [tileBatch, hc]
    exact hl.1
  have htr : tileRow L g j st + 128 ≤ P.sq := by
    simp only [tileRow, tileBlock, hrk] at hm ⊢
    omega
  exact Safety.tile_in_bounds (base := P.oBase) (fill := P.oFill) (cls := P.oClass)
    (show 64 * hh + 64 ≤ 128 by omega) htr hhd hbt

/-- **`AsyncFacts.store_bounds`**: a tensor store's box is inside its map. -/
theorem AsyncFacts_store_bounds (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) :
    ∀ {i : EvId} {a : Nat} {s : TensorStore.Spec}, X.TensorStoreIssue i a s →
      ¬ TensorHasOob s.descriptor s.origin s.rows := by
  rintro ⟨g, k⟩ a s ⟨pc, he⟩
  obtain ⟨st, hh, -, -, -, -, hw, hs⟩ := Facts.store_src hpre hX ht he
  subst hs
  have hj : arrivals (freeBar L (ctaOf L g) st) ((X.tr g).take k) < Work.T L g := by
    rw [Work.lt_T_iff hpre, ← Work.totOf_eq' hpre]
    exact hw
  exact oSpec_in_bounds hpre hj st.isLt hh.isLt

end
end PTX.Kernels.FlashAttn4Fwd.Proof
