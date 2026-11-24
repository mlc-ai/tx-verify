-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKMetadata
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderInputOrder
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderLocalAccess
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPointerInstructions
import Lemmas.Flow.NotClc

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow PTX.EventFrame
open Thread.Loader (MetadataWord)
open Thread.Loader.LocalAccessCode

noncomputable section

private theorem metadataTailCuts {cut : Nat} (hc : cut = 520 ∨ cut = 673 ∨ cut = 674)
    (bound : Nat) :
    ((kernel.code.drop cut).take (1901 - cut)).all
      (fun ins => loaderPipelineCutOp cut 1901 bound [2535, 1062] ins.op) = true := by
  rcases hc with rfl | rfl | rfl <;> (set_option maxRecDepth 100000 in kernel_rfl)

private theorem primingPointerStoreApart {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {a : Acc} {bs : List Byte} (he : X.get (g, j) = some ⟨534, .wr a bs⟩)
    (word : MetadataWord) (slot : Fin 2) : ¬ (metadataCell l g word slot).Overlap a := by
  obtain ⟨t, out, _, ht, hShape, _, hAddress, _, hFire⟩ := historyAtLoaderEvent hp hX he
    (show 506 ≤ 534 ∧ 534 < 1901 by decide) (fun _ _ => True) (fun _ _ _ => trivial)
    (by unfold HistoryStep; intros; trivial)
  have hContinues : ∃ u, out = some u := by
    cases out with
    | none =>
      obtain ⟨_, _, hf⟩ := hFire
      exact (show False by simpa [Ends] using fires_none_ends hf).elim
    | some u => exact ⟨u, rfl⟩
  obtain ⟨u, rfl⟩ := hContinues
  let pack := pointerPacket 0
  have hLoc : pack.save.active .address t.pc := by
    rw [ht]
    change (pointerPacket 0).save.active .address 534
    decide
  obtain ⟨entry, hi, _⟩ := hAddress pack.save (packetBounds 0).2.2.2.2.2.2.2
    .address hLoc
  have hReg : t.regs pack.save.loop.reg = some (b64 entry.val) := hi
  obtain ⟨_, hAt, _⟩ := pointerSaveStep hp 0 ht hShape hAddress entry hReg
    (.inr ⟨_, rfl, hFire⟩)
  obtain ⟨rfl, _⟩ := Kind.wr.inj (congrArg Event.kind (Option.some.inj hAt))
  exact metadataPointerApart (p := pointerPacket 0) (by decide) word slot entry

/-- The actual K pointer packing, reads and vectors preserve the selected V metadata
until the observed commit at the boundary of the first K packet. -/
theorem primingVMetadataAtKCommit {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g first tail batch row : Nat} (hWarp : 14 ≤ Prologue.warpIndex l g)
    {a : Acc} {bytes : List (Option Byte)}
    (hFirst : X.get (g, first) = some ⟨525, .rd a bytes⟩)
    (hTail : X.get (g, tail) = some ⟨673, .asyncCommit⟩)
    (slot : Fin 2) (hMeta : PrimingMetadataAt p l X g first batch row slot) :
    PrimingMetadataAt p l X g tail batch row slot := by
  have hOrder : first ≤ tail := by
    by_contra! h
    have hBad := Thread.Loader.eventBeforeClosedCut hp hX hWarp (cut := 673) (by decide)
      (metadataTailCuts (by decide)) hTail hFirst (by omega)
      (show 173 < 525 by decide) (show 525 < 673 by decide)
    change 673 < 673 at hBad
    omega
  intro word
  obtain ⟨w, hw, hStored, hLast⟩ := hMeta word
  refine ⟨w, by omega, hStored, ?_⟩
  intro byte hb j hj dst hWrite hCover
  by_cases hBefore : j < first
  · exact hLast byte hb j hBefore dst hWrite hCover
  have hLocal : dst.loc.space = .local := hCover.1.symm
  rcases hWrite with ⟨_, _, hImpossible⟩ | ⟨data, hWrite, _⟩ | ⟨_, _, hRmw⟩
  · cases hImpossible
  · obtain ⟨site, hs, hEvent⟩ := Thread.Loader.localWriteSite hX hWrite hLocal
    have hDecoded : (kernel.code[site.accessPc]?).any (fun ins => writeOp ins.op) = true := by
      rcases get_source hX hEvent with ⟨_, hf⟩ | ⟨_, ins, _, _, hc, hf⟩
      · cases hf
      · rw [hc, Option.any_some, fires_write_op hf rfl]
    have hAudit : scalarSites.all (fun s =>
        !(kernel.code[s.accessPc]?).any (fun ins => writeOp ins.op) ||
        decide ((173 < s.accessPc ∧ s.accessPc < 520) ∨ s.accessPc = 534 ∨ 674 ≤ s.accessPc))
        = true := by
      set_option maxRecDepth 100000 in kernel_rfl
    have hClass := List.all_eq_true.mp hAudit site hs
    simp only [hDecoded, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hClass
    rcases hClass with hOld | hPtr | hOther
    · have hBad := Thread.Loader.eventBeforeClosedCut hp hX hWarp (cut := 520) (by decide)
        (metadataTailCuts (by decide)) hFirst hEvent (by omega) hOld.1 hOld.2
      change 525 < 520 at hBad
      omega
    · rw [hPtr] at hEvent
      exact (primingPointerStoreApart hp hX hEvent word slot
        ⟨_, Acc.covers_at hb, hCover⟩).elim
    · have hBad := Thread.Loader.eventBeforeClosedCut hp hX hWarp (cut := 674) (by decide)
        (metadataTailCuts (by decide)) hEvent hTail (by omega)
        (show 173 < 673 by decide) (show 673 < 674 by decide)
      change site.accessPc < 674 at hBad
      omega
  · exact (noActualRmw hX hRmw).elim

end
end PTX.Kernels.TmlFa4Fwd.Loader
