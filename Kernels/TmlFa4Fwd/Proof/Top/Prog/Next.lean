-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.Base
public import Kernels.TmlFa4Fwd.Proof.Top.Released
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Kernels.TmlFa4Fwd.Flow.Code.Part029
import Kernels.TmlFa4Fwd.Proof.Mma.Export.AllocNext
import Kernels.TmlFa4Fwd.Proof.Protocol.Shared.MemOrdered
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Ops
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Words
import Kernels.TmlFa4Fwd.Proof.Top.Safety

@[expose] public section

/-! # E5a: the execution facts of a released lane's step outside `Rest`

The progress class this file owns: what `nonRest_steps` (`Top/Released.lean`) needs of the
execution besides the kernel facts it proves (`NextPrem`). `Prog.next` proves `NextPrem` from
`Base`: the order at the bytes that are read is `reads_ordered`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0}

/-- A lane whose last event is an allocation request of lane 0 is not at a store: it is at the
allocation's second event. -/
theorem Prog.allocLast (hp : Pre p L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) {g : Nat} {σ : (thread p L g).D}
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some σ)) {ins : Instr}
    (hins : kernel.code[(thread p L g).pc σ]? = some ins) (hst : Descent.opKind ins.op = .store)
    {pc : Nat} {grp : CtaGroup} {dst : Option Loc} {n : Nat}
    (he : X.get (g, (X.tr g).length - 1) = some ⟨pc, .tc (.resource grp dst (.alloc n))⟩) :
    laneOf L g ≠ 0 := by
  intro hl
  have hw := ((tmem1Ops hp hX (launchFollow hp hX)).event (Frame.lt_of_get hX he) he).1
  have hlen : 0 < (X.tr g).length := by
    have := (List.getElem?_eq_some_iff.mp
      (show (X.tr g)[(X.tr g).length - 1]? = _ from he)).1
    omega
  have hpc := Mma.alloc_next hp hX hw hl he (σ := σ)
    (by rw [Nat.sub_add_cancel hlen]; exact hσ)
  rw [hpc] at hins
  obtain rfl := Option.some.inj (hins.symm.trans Flow.code_1909)
  cases hst

/-- A read with a source at each byte keeps the assumptions' constraints: no write covers an input
byte it reads (`noInputWrite`). -/
theorem Prog.readWf (hp : Pre p L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X) {g pc : Nat} {a : Acc}
    {bs : List (Option Byte)} {r : Nat → Option AsyncCopy.Ref}
    (hr : ∀ e, NewRead L m X g e r a bs) :
    ∀ a' ∈ Assumptions.all, a'.wf L m (X.snoc g ⟨pc, .rd a bs⟩ r) :=
  Assumptions.wf_snoc_read hX (hr ⟨pc, .rd a bs⟩) fun _ _ _ hin w a' _ hw hcov =>
    noInputWrite hp hX hFw ⟨w, a', _, hw.intent, hcov, hin⟩

/-- **The execution facts of a released lane's step outside `Rest`**. -/
theorem Prog.next (hp : Pre p L m)
    (_hs : SafeGoal kernel Assumptions.all L m) : NextPrem p L m :=
  ⟨fun _ hm => reads_ordered hp hm.1 (launchFollow hp hm.1),
    fun _ hm _ _ _ _ _ hr => Prog.readWf hp hm.1 (launchFollow hp hm.1) hr,
    fun _ hm _ _ _ h => Tm.words hp hm.1 (launchFollow hp hm.1) h,
    fun _ hm _ _ hσ _ hins hst _ _ _ _ he => Prog.allocLast hp hm.1 hσ hins hst he⟩

end PTX.Kernels.TmlFa4Fwd.Proof.Top
