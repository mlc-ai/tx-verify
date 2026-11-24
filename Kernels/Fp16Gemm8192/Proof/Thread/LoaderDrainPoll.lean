-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ClcPoll
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderDiscipline

@[expose] public section

/-! # A loader's tail drain polls

A loader at its tail drain of slot `i` polls that slot's empty barrier in its CTA with parity 1,
succeeding or failing; after a failed poll it is still at that drain site (`loader_drain_poll`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

namespace Loader

/-- The drain's instruction is the empty wait with the acquire flag. -/
theorem drain_op {l : D} {i : Fin 4} {ins : Instr} (hs : l.site = .drain i)
    (hc : kernel.code[l.site.pc]? = some ins) :
    ∃ p b off par, ins.op = .mbarWait p b off par true .cta := by
  obtain ⟨b, par, hb⟩ := code_drain i
  rw [hs] at hc
  obtain rfl := Option.some.inj (hc.symm.trans hb)
  exact ⟨_, _, _, _, rfl⟩

/-- A failed drain poll leaves the loader at its drain. -/
theorem drain_next {L : Launch} {g : Nat} {l : D} {i : Fin 4} (hs : l.site = .drain i) {m : Loc}
    {p : Nat} {acq : Bool} {sc : MbarScope} :
    (code L g).next (.inr (.loader l)) ⟨l.site.pc, .wait m p false acq sc⟩ =
      some (some (.inr (.loader l))) := by
  obtain ⟨s, m', n, q, cp, r, x⟩ := l
  simp only at hs
  subst hs
  simp [code, Loader.next]

end Loader

set_option maxHeartbeats 8000000 in
/-- A loader at its tail drain of slot `i`, after its whole trace, can poll that slot's empty
barrier with parity 1, succeeding or failing; after a failed poll it is still at the drain. -/
theorem loader_drain_poll {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}
    (hpre : Pre P L mem0) (hg : g < L.threads) {l : Loader.D} {i : Fin 4} {t : TState}
    (hσ : (code L g).toMachine.after (some (code L g).init) (X.tr g) =
      some (some (.inr (.loader l))))
    (hs : l.site = .drain i) (hr : Run kernel Prod L g {} (X.tr g) (some t)) (ok : Bool) :
    ∃ t1 u sc, Relation.ReflTransGen (Tau kernel Prod L g) t t1 ∧
      EStep kernel Prod L g t1 ⟨(Loader.Site.drain i).pc,
        .wait (InputRing.emptyLoc L (g / L.block) i) 1 ok true sc⟩ (some u) ∧
      (ok = false → (code L g).toMachine.after (some (code L g).init) (X.tr g ++
        [⟨(Loader.Site.drain i).pc, .wait (InputRing.emptyLoc L (g / L.block) i) 1 false true
          sc⟩]) = some (some (.inr (.loader l)))) := by
  have hpc : (code L g).pc (.inr (.loader l)) = (Loader.Site.drain i).pc := by
    show l.site.pc = _
    rw [hs]
  have := poll_gen hpre hg hσ (loc := InputRing.emptyLoc L (g / L.block) i) (ph := 1)
    (fun hc => Loader.drain_op hs hc)
    (fun {t ins e o} hinv hat hc hf => by
      obtain ⟨ok, acq, sc, he⟩ := Loader.drain_event hpre i hs hat hc hf
      exact ⟨ok, acq, sc, he⟩)
    (fun {_ _ _ _} => Loader.drain_next hs) hr ok
  rw [hpc] at this
  exact this

end

end PTX.Kernels.Fp16Gemm8192.Proof
