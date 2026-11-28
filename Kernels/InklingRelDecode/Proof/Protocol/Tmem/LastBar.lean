-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Tmem.BarRound
import Kernels.InklingRelDecode.Proof.Lib.BarOne
import Kernels.InklingRelDecode.Proof.Lib.BarZero
import Lemmas.Protocol.CountNth

@[expose] public section

/-! # The last mandatory rendezvous before an event

A data lane with a mandatory rendezvous before an event has its last one before it: the rendezvous
whose earlier ones number one fewer. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Tmem
open PTX PTX.Flow

variable {Q L m X} {t : Nat}

private def mandatoryEv (e : Event) : Bool :=
  e.pc == 2241 || e.pc == 2251 || e.pc == 999 || e.pc == 1012

private theorem mandatory_eq (es : List Event) :
    Softmax.Export.mandatory es = es.countP mandatoryEv := by
  induction es with
  | nil => simp [Softmax.Export.mandatory]
  | cons e es ih =>
    unfold Softmax.Export.mandatory at ih ⊢
    simp only [List.countP_cons,mandatoryEv] at ih ⊢
    by_cases h1 : e.pc = 2241 <;> by_cases h2 : e.pc = 2251 <;> by_cases h3 : e.pc = 999 <;>
      by_cases h4 : e.pc = 1012 <;> simp [h1,h2,h3,h4] at ih ⊢ <;> omega

private theorem zero_sites : ∀ pc, (pc = 2241 ∨ pc = 2251 ∨ pc = 999 ∨ pc = 1012) →
    Lib.zeroSite pc = true := by
  rintro pc (rfl|rfl|rfl|rfl) <;> decide +kernel

/-- **The last mandatory rendezvous before an event.** -/
public theorem last_bar (hX : Consistent L kernel Assumptions.all m X) (hb : L.block = 256) {sk}
    (nu : ∀ i ev, i < sk → X.get (t,i) = some ev → ∀ f, ev.kind ≠ .ub f)
    (pos : 1 ≤ Softmax.Export.mandatory ((X.tr t).take sk)) :
    ∃ jb pc c, jb < sk ∧ X.get (t,jb) = some ⟨pc,.bar 0 c .sync⟩ ∧
      (pc = 2241 ∨ pc = 2251 ∨ pc = 999 ∨ pc = 1012) ∧
      Softmax.Export.mandatory ((X.tr t).take jb) + 1 =
        Softmax.Export.mandatory ((X.tr t).take sk) := by
  rw [mandatory_eq] at pos ⊢
  obtain ⟨j,ev,hj,hm,hc⟩ := MbarRing.Slot.exists_nth_countP mandatoryEv
    (xs := (X.tr t).take sk) (show ((X.tr t).take sk).countP mandatoryEv - 1 + 1 ≤ _ by omega)
  have lt : j < sk := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  have hget : X.get (t,j) = some ev := by
    change (X.tr t)[j]? = some ev
    rw [← List.getElem?_take_of_lt lt]
    exact hj
  rw [List.take_take,Nat.min_eq_left lt.le] at hc
  have pcs : ev.pc = 2241 ∨ ev.pc = 2251 ∨ ev.pc = 999 ∨ ev.pc = 1012 := by
    simp only [mandatoryEv,Bool.or_eq_true,beq_iff_eq] at hm
    omega
  have isb := Lib.zero_event hX hb hget (nu j ev lt hget)
  rw [zero_sites _ pcs] at isb
  obtain ⟨pc,kind⟩ := ev
  cases kind <;> simp [Execution.isBarId] at isb
  rename_i id cnt md
  subst isb
  obtain ⟨rfl,-⟩ := Lib.recorded_bar hX hb hget
  have mj := mandatory_eq ((X.tr t).take j)
  exact ⟨j,pc,cnt,lt,hget,pcs,by rw [mj]; omega⟩

end PTX.Kernels.InklingRelDecode.Proof.Tmem
