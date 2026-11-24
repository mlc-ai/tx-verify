-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueInit
public import Lemmas.Flow.NotObject
public import Lemmas.Flow.BitForms

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd
open PTX PTX.Proof Prologue

noncomputable section

/-- Offsets of the initialized CTA mbarriers in the frozen shared-memory layout. -/
def initializedMbarOffset (offset : Nat) : Prop :=
  offset % 8 = 0 ∧ (offset ≤ 232 ∨ 320 ≤ offset ∧ offset ≤ 344)

/-- Each aligned offset of the two initialized intervals names the exact physical object
of a decoded initializer. -/
theorem initObjectOfOffset {l : Launch} {cta offset : Nat}
    (h : initializedMbarOffset offset) :
    ∃ i : Fin 34, ⟨.shared, cta, l.sharedBase + offset⟩ = initObject l cta i := by
  obtain ⟨ha, hs | ⟨hl, hh⟩⟩ := h
  · let j : Fin 30 := ⟨offset / 8, by omega⟩
    have hf (i : Fin 30) :
        (initSite ⟨i.val, by omega⟩).baseOffset + (initSite ⟨i.val, by omega⟩).displacement =
          8 * i.val := by
      fin_cases i <;> rfl
    refine ⟨⟨j.val, by omega⟩, ?_⟩
    unfold initObject
    have hoff : 8 * j.val = offset := by dsimp [j]; omega
    rw [Nat.add_assoc, hf j, hoff]
  · let j : Fin 4 := ⟨(offset - 320) / 8, by omega⟩
    have hf (i : Fin 4) :
        (initSite ⟨30 + i.val, by omega⟩).baseOffset +
          (initSite ⟨30 + i.val, by omega⟩).displacement = 320 + 8 * i.val := by
      fin_cases i <;> rfl
    refine ⟨⟨30 + j.val, by omega⟩, ?_⟩
    unfold initObject
    have hoff : 320 + 8 * j.val = offset := by dsimp [j]; omega
    rw [Nat.add_assoc, hf j, hoff]

section
variable {p : Params} {l : Launch} {m : Mem0}

/-- Resolve the concrete CTA location of a verified shared barrier address. -/
theorem decodedMbarOffset (hp : Pre p l m) {g : Nat} {t : TState} {base delta off : Nat}
    (hBase : t.regs base = some (b32 (l.sharedBase + delta)))
    (hOffset : initializedMbarOffset (delta + off)) :
    mbarLoc l g t base (off : Int) =
      .ok ⟨.shared, g / l.block, l.sharedBase + (delta + off)⟩ := by
  have hBound : l.sharedBase + delta + off < 2 ^ 32 := by
    have hShared := hp.shared.2.1
    have hRange := hOffset.2
    omega
  have hAlign : (l.sharedBase + delta + off) % 8 = 0 := by
    have hShared := hp.shared.1
    have hRange := hOffset.1
    omega
  simpa only [Nat.add_assoc] using mbarOff (l := l) (g := g) hBase hBound hAlign

/-- A poll's decoded base and displacement identify its exact shared object. -/
theorem pollResolvedMbarAddress {A : List Assumption} (hp : Pre p l m)
    {g pc pred base delta off : Nat} {t : TState} {phase : Opnd} {acq : Bool} {scope : MbarScope}
    {e : Event} {o : Option TState} (hBase : t.regs base = some (b32 (l.sharedBase + delta)))
    (hOff : initializedMbarOffset (delta + off))
    (hf : Fires pc (eventTmpl A l g t (.mbarWait pred base off phase acq scope)) e o) {target : Loc}
    {q : Nat} {ok acq' : Bool} {scope' : MbarScope} (hk : e.kind = .wait target q ok acq' scope') :
    target = ⟨.shared, g / l.block, l.sharedBase + (delta + off)⟩ :=
  Flow.fires_wait_loc (decodedMbarOffset hp hBase hOff) hf _ _ _ _ _ hk

/-- A CTA arrival's decoded base and displacement identify its exact shared object. -/
theorem arriveResolvedMbarAddress {A : List Assumption} (hp : Pre p l m) {g pc base delta off : Nat}
    {t : TState} {bytes count : Opnd} {rel : Bool} {scope : MbarScope} {dst : Option Nat}
    {e : Event} {o : Option TState} (hBase : t.regs base = some (b32 (l.sharedBase + delta)))
    (hOff : initializedMbarOffset (delta + off))
    (hf : Fires pc (eventTmpl A l g t (.mbarArrive base off bytes count false rel scope dst)) e o)
    {target : Loc} {tx n : Nat} {rel' : Bool} {scope' : MbarScope}
    (hk : e.kind = .arrive target tx n rel' scope') :
    target = ⟨.shared, g / l.block, l.sharedBase + (delta + off)⟩ := by
  have hLoc := decodedMbarOffset (g := g) hp hBase hOff
  exact Flow.fires_arrive_loc (cluster := false) hLoc hf target tx n rel' scope' hk
end

variable {p : Params} {l : Launch} {m : Mem0} {A : List Assumption} (hp : Pre p l m)
    {g pc base delta off : Nat} {t : TState} (hg : g < l.threads)
    (hBase : t.regs base = some (b32 (l.sharedBase + delta)))
    (hOff : initializedMbarOffset (delta + off)) {e : Event} {o : Option TState}
    (hf : Fires pc (eventTmpl A l g t (.tcCommit .one base off none)) e o) {spec : TcCommit.Spec}
    (hk : e.kind = .tc (.commit spec)) {rank : Fin 16}
include hp hg hBase hOff hf hk

/-- An unmasked single-CTA commit targets the shared address selected by its operands. -/
theorem commitExactAddress {target : Loc} (hTarget : TcCommit.target spec rank = some target) :
    target = ⟨.shared, g / l.block, l.sharedBase + (delta + off)⟩ := by
  let loc : Loc := ⟨.shared, g / l.block, l.sharedBase + (delta + off)⟩
  have hBound : l.sharedBase + delta + off < 2 ^ 32 := by
    have hShared := hp.shared.2.1
    have hRange := hOff.2
    omega
  have hAlign : (l.sharedBase + delta + off) % 8 = 0 := by
    have hShared := hp.shared.1
    have hRange := hOff.1
    omega
  have hAddr : mbarClusterLoc l g t base (off : Int) = .ok loc := by
    rw [show loc = ⟨.shared, g / l.block, l.sharedBase + delta + off⟩ by
      simp only [loc, Nat.add_assoc]]
    exact Flow.mbarClusterLoc_off hBase hBound hAlign
  let expected : TcCommit.Spec := ⟨.one, loc, 1, g / l.block, 1⟩
  have hBlock : 0 < l.block := by rw [hp.block]; decide
  have hCta := (Nat.div_lt_iff_lt_mul hBlock).2 (show g < l.grid * l.block from hg)
  have hOne := hp.cluster.2.2
  have hRes : TcCommit.resolve l .one (g / l.block) loc
      (BitVec.ofNat 16 (2 ^ l.rankOfCta loc.cta)) = some expected := by
    simp [TcCommit.resolve, expected, loc, hp.launch.1, hCta, Launch.oneDim_rankOfCta hOne,
      Launch.oneDim_clusterOfCta hOne, Launch.oneDim_clusterStart hOne,
      Launch.oneDim_clusterSizeOf hOne, hp.cluster.1, Nat.mod_one]
  simp only [eventTmpl, tcCommitTmpl, hg, ↓reduceIte, hAddr, bind, Except.bind,
    pure, Except.pure, hRes, ofExec] at hf
  obtain ⟨rfl, _⟩ := hf
  change Kind.tc (.commit expected) = Kind.tc (.commit spec) at hk
  simp only [Kind.tc.injEq, TcKind.commit.injEq] at hk
  subst spec
  unfold TcCommit.target at hTarget
  split at hTarget
  · rename_i hRank
    have hr : rank.val = 0 := by
      have hLt : rank.val < 1 := hRank.1
      omega
    have hLoc : target = loc := by
      simpa only [expected, loc, hr, Nat.add_zero] using Option.some.inj hTarget.symm
    exact hLoc
  · cases hTarget

end
end PTX.Kernels.TmlFa4Fwd
