-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.DataOrdinal
public import Kernels.InklingRelDecode.Proof.Common.PublicationPrefix
public import Kernels.InklingRelDecode.Proof.Common.Table
public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Common.LaunchRounds
public import Kernels.InklingRelDecode.Proof.Lib.BarSchedule
import all Kernels.InklingRelDecode.Proof.Common.Follow
import Kernels.InklingRelDecode.Proof.Common.LaunchLane
import Kernels.InklingRelDecode.Proof.Common.ShuffleOrdinal
import Kernels.InklingRelDecode.Proof.Common.Where
import Mathlib.Tactic.FinCases

@[expose] public section

/-! # The pc of a data lane's rendezvous, by its ordinal

At a state of a data thread that stands at a rendezvous, the pc is the entry of the schedule
`Lib.dataBar` at the position `t` = (barrier-zero count) + (barrier-one count) - (visits of the
optional rescale rendezvous 2326). The rescale rendezvous itself stands where `dataBar` has the
round's fourth rendezvous (999). -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Flow PTX.Frame

noncomputable section

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- What a data state at a rendezvous says about its pc, given its counts. -/
def DataBarAt (Q : Params) (L : Launch) (g : Nat) (d : (thread Q L g).D) : Prop :=
  let t := d.2 (.bar 0) + publication d - d.2 (.atPc 2326)
  (thread Q L g).pc d = Lib.dataBar (Iface.preloadCount Q L (g/L.block))
      (Lib.blocksOf Q L (g/L.block)) t ∨
    ((thread Q L g).pc d = 2326 ∧ Lib.dataBar (Iface.preloadCount Q L (g/L.block))
      (Lib.blocksOf Q L (g/L.block)) t = 999)

abbrev BarSitePc (pc : Nat) : Prop := pc ∈ Lib.barOneSites ∨ Lib.zeroSite pc = true

private theorem start_bar (s : Startup.Site) (h : BarSitePc s.pc) : s = .bar0 ∨ s = .bar1 := by
  cases s <;> first | (left; rfl) | (right; rfl) | (exfalso; revert h; decide) |
    (rename_i r; cases r <;> (exfalso; revert h; decide))

private theorem pro_bar (s : Prologue.Site) (h : BarSitePc s.pc) :
    s = .bar2 ∨ (∃ b j, s = .pb b j) ∨ s = .bar18 := by
  cases s <;> first | (left; rfl) | (right; right; rfl) | (right; left; exact ⟨_,_,rfl⟩) |
    (exfalso; revert h; repeat' first | decide +kernel | (rename_i j; revert j))

private theorem soft_bar (s : Softmax.Site) (h : BarSitePc s.pc) :
    s = .bar0 ∨ s = .bar20 ∨ s = .bar21 ∨ s = .bar22 ∨ s = .bar23 ∨ s = .bar24 := by
  cases s <;> first | (left; rfl) | (right; left; rfl) | (right; right; left; rfl) |
    (right; right; right; left; rfl) | (right; right; right; right; left; rfl) |
    (right; right; right; right; right; rfl) |
    (exfalso; revert h; repeat' first | decide +kernel | (rename_i j; revert j))

private theorem epi_bar (s : Epilogue.Site) (h : BarSitePc s.pc) :
    s = .join ∨ s = .sync1 ∨ s = .sync0 := by
  cases s <;> first | (left; rfl) | (right; left; rfl) | (right; right; rfl) |
    (exfalso; revert h; repeat' first | decide +kernel | (rename_i j; revert j))

private theorem pb_pc (p lim : Nat) (b : Fin 3) (j : Fin 5) (hb : b.val < p) :
    Lib.dataBar p lim (3+5*b.val+j.val) = Prologue.pbPc b j := by
  rw [Lib.dataBar_block p lim b.val j.val hb j.2]
  fin_cases b <;> fin_cases j <;> rfl

theorem data_bar_state {k s n} (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) (hk : k ≤ (X.tr g).length)
    (hs : stateAt (thread Q L) X g k = some (some (s,n))) (nu : NoUbBefore X g k)
    (tab : tableInv Q L g (s,n)) (lg : g%L.block<128)
    (bar : BarSitePc ((thread Q L g).pc (s,n))) : DataBarAt Q L g (s,n) := by
  rcases s with st | ⟨r, d⟩
  · have lc := startup_counts hp hX hk hs nu
    have c : n (.atPc 2326) = 0 := lc.visit 2326 (by decide)
    have z := lc.first
    change BarSitePc st.site.pc at bar
    have e := Lib.dataBar_startup (Iface.preloadCount Q L (g/L.block))
      (Lib.blocksOf Q L (g/L.block))
    rcases start_bar _ bar with h | h <;> simp only [DataBarAt, publication, c, z, h]
    · exact .inl e.1.symm
    · exact .inl e.2.1.symm
  rcases r with r | r
  swap
  · change BarSitePc (Startup.Entry.pc r) at bar
    exfalso
    cases r <;> revert bar <;> decide
  cases r with
  | dispatch w x =>
    have := (worker_warp hp hX hk hs).1
    omega
  | prologue w =>
    rcases d with d | ⟨ent, d | ⟨u, d⟩⟩
    · obtain ⟨-, -, hist⟩ := tab
      have z := preload_ordinal hp hX hk hs nu
      have c := preload_clear hp hX hk hs nu
      change BarSitePc d.site.pc at bar
      simp only [DataBarAt, publication, dataPublication, c, z]
      rcases pro_bar _ bar with h | ⟨b, j, h⟩ | h <;> rw [h]
      · exact .inl (Lib.dataBar_startup _ _).2.2.symm
      · have large : 41 < d.site.pc := by rw [h]; fin_cases b <;> fin_cases j <;> decide
        have cap := Prologue.preload_count hp hg (hist.known.first (by omega))
          (hist.known.last (by omega)) (hist.known.seq large)
        have bl := hist.block b (by rw [h]; rfl)
        have : b.val < Iface.preloadCount Q L (g/L.block) := by
          rw [← cap]; have := b.2; omega
        refine .inl ?_
        have pos : Prologue.preloadPosition (Iface.preloadCount Q L (g/L.block)) (.pb b j) +
            Prologue.publicationPhase (.pb b j) - 0 = 3+5*b.val+j.val := by
          simp [Prologue.preloadPosition, Prologue.publicationPhase]
        rw [pos, pb_pc _ _ b j this]
        rfl
      · exact .inl (Lib.dataBar_publish _ _).1.symm
    · obtain ⟨⟨inv, -⟩, -⟩ := tab
      have z := data_ordinal hp hX hk hs nu
      have prev := shfl_previous hp hX hk hs nu
      have lim := reached_limit hp hX hg hk hs
      change BarSitePc d.site.pc at bar
      simp only [DataBarAt, publication, dataPublication, softPublication, ← lim]
      obtain ⟨site, i, v⟩ := d
      have round (r : Nat) (hr : r < 4) (hl : i < ent.limit) (h2 : 2 ≤ 4*i+r)
          (hT : n (.bar 0) + Softmax.publicationPhase site - n (.atPc 2326) =
            3+5*Iface.preloadCount Q L (g/L.block)+(4*i+r)) :
          Lib.dataBar (Iface.preloadCount Q L (g/L.block)) ent.limit
            (n (.bar 0) + Softmax.publicationPhase site - n (.atPc 2326)) = Lib.roundBar r := by
        rw [hT]
        exact Lib.dataBar_round _ _ i r hr hl h2
      rcases soft_bar _ bar with h | h | h | h | h | h <;> subst h
      · have i0 : i = 0 := inv.init (.inr rfl)
        subst i0
        have z' : n (.bar 0)+2 = 3+5*Iface.preloadCount Q L (g/L.block)+2+n (.atPc 2326) := by
          simpa [Softmax.fixedCount, Softmax.syncPosition] using z
        have hT : n (.bar 0) + Softmax.publicationPhase .bar0 - n (.atPc 2326) =
            3+5*Iface.preloadCount Q L (g/L.block)+1 := by
          simp only [Softmax.publicationPhase]
          omega
        rw [hT]
        exact .inl (Lib.dataBar_publish _ _).2.symm
      all_goals have loop : i < ent.limit := inv.loop nofun nofun nofun (fun _ => nofun)
      · have z' : n (.bar 0)+2 = 3+5*Iface.preloadCount Q L (g/L.block)+(4*i+2)+n (.atPc 2326) := by
          simpa [Softmax.fixedCount, Softmax.syncPosition] using z
        exact .inl ((round 2 (by omega) loop (by omega) (by
          simp only [Softmax.publicationPhase]; omega)).symm)
      · have z' : n (.bar 0)+2 = 3+5*Iface.preloadCount Q L (g/L.block)+(4*i+3)+n (.atPc 2326) := by
          simpa [Softmax.fixedCount, Softmax.syncPosition] using z
        exact .inl ((round 3 (by omega) loop (by omega) (by
          simp only [Softmax.publicationPhase]; omega)).symm)
      · have pos : 0 < i := prev rfl
        have z' : n (.bar 0)+2 = 3+5*Iface.preloadCount Q L (g/L.block)+(4*i+0)+n (.atPc 2326) := by
          simpa [Softmax.fixedCount, Softmax.syncPosition] using z
        exact .inl ((round 0 (by omega) loop (by omega) (by
          simp only [Softmax.publicationPhase]; omega)).symm)
      · have pos : 0 < i := prev rfl
        have z' : n (.bar 0)+2 = 3+5*Iface.preloadCount Q L (g/L.block)+(4*i+1)+n (.atPc 2326) := by
          simpa [Softmax.fixedCount, Softmax.syncPosition] using z
        exact .inl ((round 1 (by omega) loop (by omega) (by
          simp only [Softmax.publicationPhase]; omega)).symm)
      · have z' : n (.bar 0)+2 = 3+5*Iface.preloadCount Q L (g/L.block)+(4*i+2)+n (.atPc 2326) := by
          simpa [Softmax.fixedCount, Softmax.syncPosition] using z
        exact .inr ⟨rfl, round 2 (by omega) loop (by omega) (by
          simp only [Softmax.publicationPhase]; omega)⟩
    · cases u
      have z := epilogue_ordinal hp hX hk hs nu
      have lim := reached_limit hp hX hg hk hs
      change BarSitePc d.site.pc at bar
      simp only [DataBarAt, publication, dataPublication, softPublication, ← lim]
      obtain ⟨site, v⟩ := d
      have fc : Softmax.fixedCount ⟨.epilogue, ent.limit, {}⟩ = Lib.loopEnd ent.limit := by
        simp [Softmax.fixedCount, Softmax.syncPosition, Lib.loopEnd]
      rw [fc] at z
      have e := Lib.dataBar_epilogue (Iface.preloadCount Q L (g/L.block)) ent.limit
      rcases epi_bar _ bar with h | h | h <;> subst h <;> refine .inl ?_
      · have hT : n (.bar 0) + Epilogue.publicationPhase .join - n (.atPc 2326) =
            3+5*Iface.preloadCount Q L (g/L.block)+Lib.loopEnd ent.limit := by
          simp [Epilogue.publicationPhase, Epilogue.Site.pc, Lib.afterFinal] at z ⊢
          omega
        rw [hT]
        exact e.1.symm
      · have hT : n (.bar 0) + Epilogue.publicationPhase .sync1 - n (.atPc 2326) =
            3+5*Iface.preloadCount Q L (g/L.block)+Lib.loopEnd ent.limit+1 := by
          simp [Epilogue.publicationPhase, Epilogue.Site.pc, Lib.afterFinal] at z ⊢
          omega
        rw [hT]
        exact e.2.1.symm
      · have hT : n (.bar 0) + Epilogue.publicationPhase .sync0 - n (.atPc 2326) =
            3+5*Iface.preloadCount Q L (g/L.block)+Lib.loopEnd ent.limit+2 := by
          simp [Epilogue.publicationPhase, Epilogue.Site.pc, Lib.afterFinal] at z ⊢
          omega
        rw [hT]
        exact e.2.2.symm

/-- The state before a fault-free event, with the guarded table facts. -/
theorem event_table {k e} (hf : Follow Q L X) (hX : Consistent L kernel Assumptions.all m X)
    (hp : Pre Q L m) (he : X.get (g,k) = some e) (clean : ∀ f, e.kind ≠ .ub f) :
    ∃ d, stateAt (thread Q L) X g k = some (some d) ∧ guardedTable Q L g d := by
  have hg := Frame.lt_of_get hX he
  exact Frame.good_stateU (J := guardedTable Q L) (fun g hg => thread_sound hp hg) hX he
    (fun _ f eq => clean f (congrArg Event.kind eq)) (hf g hg k)

end
end PTX.Kernels.InklingRelDecode.Proof
