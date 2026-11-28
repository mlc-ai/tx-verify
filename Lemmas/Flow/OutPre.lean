-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.OutRunCond

@[expose] public section

/-! # The state a path has reached inside a run of items

`xRun_path` says that a state the local steps reach from the start of a run is the state after a
prefix of the items, or goes on from the end. When no local path leads back from the end into the
run (the run ends at an event or inside a region that keeps going), a state at a position inside
the run is the state after the prefix up to its position (`xItems_pre`). Two runs that follow each
other are one run (`OAt.append`). -/

namespace PTX.Flow
open PTX PTX.Proof PTX.Assumption

noncomputable section
variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

theorem OAt.append : ∀ {pc : Nat} {a b : List XItem}, OAt K A L g pc a →
    OAt K A L g (pc + a.length) b → OAt K A L g pc (a ++ b)
  | _, [], b, _, h => h
  | pc, _ :: a, b, h, h' => ⟨h.1, OAt.append h.2 (by
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using h')⟩

/-- **A state inside a run of items** is the state after the prefix of the items up to its
position, with that prefix's registers. -/
theorem xItems_pre {items : List XItem} {V : Nat → Value} {dom : List Nat} {u t : TState}
    (hat : OAt K A L g u.pc items) (hf : u.fault = none)
    (hd : ∀ r ∈ dom, u.regs r = some (V r)) (hrd : xReadsB dom items = true)
    (hq : xReq V items = true) (hl : xLocalB items = true)
    (hr : Relation.ReflTransGen (Tau K A L g) u t)
    (hno : ∀ t1 t', t1.pc = u.pc + items.length → Relation.ReflTransGen (Tau K A L g) t1 t' →
      ¬ (u.pc ≤ t'.pc ∧ t'.pc < u.pc + items.length))
    (h1 : u.pc ≤ t.pc) (h2 : t.pc < u.pc + items.length) :
    ∃ j < items.length, t.pc = u.pc + j ∧
      ∀ r ∈ xWrites (items.take j) ++ dom, t.regs r = some (xFinal V (items.take j) r) := by
  obtain ⟨j, hj, t1, a1, a2, a3, a4, -, -, -, -, -, a10⟩ := xRun_path items V dom u
    hat.code hf hd hrd hq hl hat.rules t hr
  rcases a2 with rfl | rfl
  · exact absurd ⟨h1, h2⟩ (hno t1 t (by omega) a1)
  · refine ⟨j, by omega, by omega, a10⟩

end
end PTX.Flow
