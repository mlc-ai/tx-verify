-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.CtaBarrier.CtaBarrierIdentity
public import Lemmas.CtaBarrier.CtaBarrierReplaceOrder
public import Lemmas.Order.DependencyWitness

@[expose] public section

namespace PTX
noncomputable section
variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {c : Nat} {records : List (CtaBarrier.Record EvId)}

/-- Extending only a checked CTA resource history cannot create synchronization
between old source events. A passed receiver already belongs to a released phase;
appended arrivals cannot join that past phase. -/
theorem sync_withCtaHistory_iff (hX : Consistent L K A mem0 X)
    (hp : X.barriers c <+: records) (hh : CtaBarHistoryOk L (X.withCtaHistory c records))
    {e f : EvId} : CtaBarSync L (X.withCtaHistory c records) e f ↔ CtaBarSync L X e f := by
  let Y := X.withCtaHistory c records
  have hle : X.le Y := X.le_withCtaHistory c hp
  constructor
  · rintro ⟨hcta,key,i,j,hki,hkj,hei,hjf,hflen⟩
    obtain ⟨count,pc,hbar⟩ := hkj.2.1
    have hpass : j+1 < (X.tr f.1).length := by
      change f.2 < (X.tr f.1).length at hflen
      omega
    obtain ⟨oldkey,hOld,hDone⟩ := ctaBarDone_of_returned hX hbar hpass
    have hkey := CtaBarK.key_unique hh hkj (hOld.mono hle)
    subst key
    have hSender : CtaBarArrivalK L X (e.1,i) oldkey := by
      by_cases hec : e.1/L.block = c
      · have hb : 0 < L.block := by
          have hg := hcta.1
          unfold Launch.threads at hg
          by_contra hn
          have hz : L.block = 0 := by omega
          rw [hz,Nat.mul_zero] at hg
          omega
        have hc : c < L.grid := by
          rw [←hec]
          exact (Nat.div_lt_iff_lt_mul hb).mpr hcta.1
        obtain ⟨last,hlast⟩ := (hX.ctaBar.2 c hc).2.2
        obtain ⟨suffix,hsuffix⟩ := hp
        have hgen : CtaBarrier.GenerationOf L.block (X.barriers c ++ suffix)
            (e.1,i) (oldkey%16) (oldkey/16) := by
          have hg := hki.2.2
          change CtaBarrier.GenerationOf L.block
            (if e.1/L.block = c then records else X.barriers (e.1/L.block))
            (e.1,i) (oldkey%16) (oldkey/16) at hg
          rw [ite_eq_left hec,←hsuffix] at hg
          exact hg
        rcases hgen.append_cases hlast with hg | hlater
        · refine ⟨hki.1,hki.2.1,?_⟩
          change CtaBarrier.GenerationOf L.block (X.barriers (e.1/L.block))
            (e.1,i) (oldkey%16) (oldkey/16)
          rw [hec]
          exact hg
        · have hfc : f.1/L.block = c := hcta.2.2.symm.trans hec
          have hd : CtaBarrier.Released L.block (X.barriers c) (oldkey%16) (oldkey/16) := by
            simpa only [CtaBarDone,hfc] using hDone
          have hlt := CtaBarrier.released_generation_lt hlast hd
          omega
      · exact (ctaBarArrivalK_withCtaHistory_other (e := (e.1,i)) hec).mp hki
    exact ⟨hcta,oldkey,i,j,hSender,hOld,hei,hjf,hflen⟩
  · intro hs
    exact hs.mono hle

/-- All memory-order consequences remain fixed when only checked barrier-resource
records grow over a fixed, previously consistent source execution. -/
theorem baseCausality_withCtaHistory_iff (hX : Consistent L K A mem0 X)
    (hp : X.barriers c <+: records) (hh : CtaBarHistoryOk L (X.withCtaHistory c records)) :
    ∀ e f, baseCausality L (X.withCtaHistory c records) e f ↔ baseCausality L X e f := by
  have hbase : ∀ e f,
      (po (X.withCtaHistory c records) e f ∨ CtaBarSync L (X.withCtaHistory c records) e f ∨
        MSync L (X.withCtaHistory c records) e f ∨ ClusterSync L (X.withCtaHistory c records) e f ∨
        WarpBarSync L (X.withCtaHistory c records) e f ∨
        synchronizesWith L (X.withCtaHistory c records) e f ∨
        FenceSync L (X.withCtaHistory c records) e f) ↔
      (po X e f ∨ CtaBarSync L X e f ∨ MSync L X e f ∨ ClusterSync L X e f ∨
        WarpBarSync L X e f ∨ synchronizesWith L X e f ∨ FenceSync L X e f) := by
    intro e f
    rw [sync_withCtaHistory_iff hX hp hh]
    rfl
  intro e f
  constructor <;> intro h
  · induction h with
    | single h => exact .single ((hbase _ _).mp h)
    | tail _ h ih => exact ih.tail ((hbase _ _).mp h)
  · induction h with
    | single h => exact .single ((hbase _ _).mpr h)
    | tail _ h ih => exact ih.tail ((hbase _ _).mpr h)

end
end PTX
