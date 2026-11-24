-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Poll
public import Lemmas.Kernel.Frame
public import Lemmas.Flow.WaitTmpl
public import Lemmas.Flow.UbStop
public import Lemmas.Flow.Ledger

@[expose] public section

/-! # A thread at a poll site of its machine polls its barrier next

The poll premise of the progress library (`Sched.PollsOn`, `Lemmas/Kernel/Progress/Poll.lean`)
from a site machine with a shape table: when a thread's state at the end of its trace sits at an
acquiring `mbarrier.try_wait`, and every shape of that state is a wait on `m` with the parity of
the thread's successful polls of `m` plus `δ` and none is undefined behaviour, the thread's next
event polls `m` with that parity (`pollsOn_of_shapeAt`, and `pollsOn_of_shape` from a whole shape
table). Stated over any sound machine family and the shapes of one state. Promoted from the
tml-fa4 progress lane (`Proof2/Lib/PollsOn.lean`). -/

namespace PTX.Frame
open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {C : (g : Nat) → Flow.Code K A L g}
  {X : Execution} {g : Nat}

/-- **A thread at a poll site of its machine polls its barrier next**: every event fired at the
site of its state `d` satisfies `P` (the state's shapes), none of which is undefined behaviour or a
wait other than one on `m` with the parity of the thread's successful polls of `m` plus `δ`. -/
theorem pollsOn_of_shapeAt (hC : ∀ g < L.threads, (C g).Sound) (hg : g < L.threads)
    {d : (C g).D} (hσ : stateAt C X g (X.tr g).length = some (some d)) {P : Event → Prop}
    (hS : ∀ {t : TState} {ins : Instr} {e : Event} {o : Option TState}, (C g).AtD d t →
      (C g).inv d → K.code[(C g).pc d]? = some ins →
      Fires ((C g).pc d) (eventTmpl A L g t ins.op) e o → P e)
    {gd : Option (Nat × Bool)} {p b : Nat} {off : Int} {par : Opnd} {sc : MbarScope}
    (hins : K.code[(C g).pc d]? = some ⟨gd, .mbarWait p b off par true sc⟩)
    {m : Loc} {δ : Nat}
    (hub : ∀ f, ¬ P ⟨(C g).pc d, .ub f⟩)
    (hev : ∀ l q ok sc', P ⟨(C g).pc d, .wait l q ok true sc'⟩ →
      l = m ∧ q % 2 = (okPolls m (X.tr g) + δ) % 2) :
    Sched.PollsOn K A L X g m δ := by
  refine ⟨(C g).pc d, (okPolls m (X.tr g) + δ) % 2, Nat.mod_mod _ _, fun t hr ok => ?_⟩
  obtain ⟨t1, ins, hl, hat, hinv, hc, hout⟩ := end_at (C := C) hC hg hr hσ
  rw [hins] at hc
  obtain rfl := (Option.some.inj hc).symm
  rcases eventTmpl_mbarWait_cases (A := A) (L := L) (g := g) (t := t1) (p := p) (b := b)
    (off := off) (par := par) (acq := true) (sc := sc) with ⟨f, hf⟩ | ⟨l, q, k, sc', hq2, htm⟩
  · refine absurd hf (not_ub_of_fires (pc := (C g).pc d) (fun f hfire => hub f ?_) f)
    exact hS hat hinv hins hfire
  have hfire : ∀ ok', Fires ((C g).pc d) (eventTmpl A L g t1 (.mbarWait p b off par true sc))
      ⟨(C g).pc d, .wait l q ok' true sc'⟩ (some (k ok')) := fun ok' => by
    rw [htm]
    exact ⟨ok', rfl, rfl⟩
  obtain ⟨rfl, hpar⟩ := hev l q true sc' (hS hat hinv hins (hfire true))
  have hq : q = (okPolls l (X.tr g) + δ) % 2 := by omega
  subst hq
  have hpc : t1.pc = (C g).pc d := hat.1
  refine ⟨t1, k ok, sc', hl, ?_⟩
  refine ⟨eventTmpl A L g t1 (.mbarWait p b off par true sc), hout, ?_⟩
  rw [hpc]
  exact hfire ok

/-- `pollsOn_of_shapeAt` with the machine's shape table. -/
theorem pollsOn_of_shape (hC : ∀ g < L.threads, (C g).Sound) (hg : g < L.threads)
    {d : (C g).D} (hσ : stateAt C X g (X.tr g).length = some (some d))
    {Ev : (C g).D → Event → Prop} (hS : (C g).Shape Ev)
    {gd : Option (Nat × Bool)} {p b : Nat} {off : Int} {par : Opnd} {sc : MbarScope}
    (hins : K.code[(C g).pc d]? = some ⟨gd, .mbarWait p b off par true sc⟩)
    {m : Loc} {δ : Nat}
    (hub : ∀ f, ¬ Ev d ⟨(C g).pc d, .ub f⟩)
    (hev : ∀ l q ok sc', Ev d ⟨(C g).pc d, .wait l q ok true sc'⟩ →
      l = m ∧ q % 2 = (okPolls m (X.tr g) + δ) % 2) :
    Sched.PollsOn K A L X g m δ :=
  pollsOn_of_shapeAt hC hg hσ (fun hat hi hc hf => hS hat hi hc hf) hins hub hev

end

end PTX.Frame
