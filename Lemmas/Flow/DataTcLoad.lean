-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.DataLoad

@[expose] public section

/-! # A value machine's data step at a Tensor Memory load

A proof tool, generic over the kernel, beside `DataStep.load` (`Lemmas/Flow/DataLoad.lean`):
`DataStep.tcLoad` reduces the data step of a `tcgen05.ld` without reduction, without
`.pack::16b` and at a site no assumption selects with `tcLdWait` to the local code after it, from
the state the event leaves: the loaded values set in the destination registers at the next pc
(`fires_tcLd`). `Reach.tcLoad` states it for a successor whose facts a `Reach` from the next pc
gives, with the loaded values zipped onto the destinations (`holds_setRegs_zip`). -/

namespace PTX.Flow.Code
open PTX PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- **The data step of a Tensor Memory load**: from the state with the loaded values. -/
theorem DataStep.tcLoad {C' : Code K A L g} {dF : C'.D → List (Nat × Value)} {d : C'.D}
    {ds : List Nat} {ta : Nat} {sh : TcShape}
    (hc : K.code[C'.pc d]? = some ⟨none, .tcLd ds ta sh none⟩) (hsh : ∀ s, sh ≠ .packed16 s)
    (hw : A.any (·.tcLdWait (C'.pc d)) = false)
    (hrun : C'.inv d → ∀ a vals d' t, C'.next d ⟨C'.pc d, .tc (.ld a vals sh)⟩ = some (some d') →
      vals.length = ds.length → C'.AtD d t →
      (∀ t', Relation.ReflTransGen (Tau K A L g) (setRegs (PTX.next t) ds vals) t' →
        Stops K A L g t' → Holds t'.regs (dF d')) ∨
        Machine.Dead (K := K) (A := A) (L := L) (g := g) (setRegs (PTX.next t) ds vals)) :
    DataStep C' dF d := by
  intro t e u d' ins hat hi hc' hf hn
  obtain rfl := Option.some.inj (hc'.symm.trans hc)
  have hw' : A.any (·.tcLdWait t.pc) = false := by rw [hat.1]; exact hw
  obtain ⟨a, vals, hl, rfl, rfl⟩ := fires_tcLd hsh hf hw'
  exact hrun hi a vals d' t hn hl hat

/-- The state after a Tensor Memory load from `t` at `p` with facts `F` is at `p + 1` with `F`
on the other registers and the loaded values on the destinations. -/
theorem at_tcLoad {t : TState} {p : Nat} {F : List (Nat × Value)} {ds : List Nat}
    {vals : List Value} (hat : At t p F) (hnd : ds.Nodup) (hoff : ∀ q ∈ F, q.1 ∉ ds) :
    At (setRegs (PTX.next t) ds vals) (p + 1) (F ++ ds.zip vals) := by
  obtain ⟨hp, hs, ha, hf, hF⟩ := hat
  obtain ⟨sp, ss, sa, sf⟩ := setRegs_skel (PTX.next t) ds vals
  refine ⟨?_, ?_, ?_, ?_, (holds_append _ _ _).mpr ⟨holds_setRegs_off (t := PTX.next t) hF hoff,
    holds_setRegs_zip (PTX.next t) ds vals hnd⟩⟩
  · rw [sp, ← hp]; rfl
  · rw [ss]; exact hs
  · rw [sa]; exact ha
  · rw [sf]; exact hf

end
end PTX.Flow.Code
