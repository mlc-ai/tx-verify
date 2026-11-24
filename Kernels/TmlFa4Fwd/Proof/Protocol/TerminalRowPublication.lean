-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalHandoff
public import Kernels.TmlFa4Fwd.Proof.Protocol.LseTerminalSources
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
open PTX PTX.Proof PTX.Flow Thread Thread.Correction Epilogue
open PTX.Kernels.TmlFa4Fwd.Correction

/-- The actual terminal softmax drain supplies the two words in the correction
wait's observed generation. The same words feed normalization and LSE. -/
theorem terminalWordsOfCompletedDrainForWait {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFootprint : OutputFootprint p X)
    {g pos : Nat} {stage : Fin 2} {sum maximum : ℝ}
    (hActive : g/l.block < tilePrefix p p.batch*p.heads)
    (hDrain : TerminalDrainValues l X g stage sum maximum)
    (hWait : CorrectionWaits X (g,pos) .terminal stage)
    (hPass : pos+1 < (X.tr g).length) :
    ∃ pub, TerminalPublishedWords l X g stage pub (fl sum) (fl maximum) ∧
      TerminalGeneration l X g stage (pub-2) pos := by
  let producer := terminalStatsProducer l g stage
  have hOwner : producer/l.block = g/l.block := terminalStatsCta hp g stage
  have hObservation := hWait
  obtain ⟨_,he,_⟩ := hObservation
  have hGrid := NamedBar.cta_lt (event_thread_lt hX he)
  have hThread : producer < l.threads := by
    rw [show l.threads = l.grid*l.block from rfl,hp.block]
    rw [hp.block] at hOwner hGrid
    have hMod := Nat.mod_lt producer (show 0 < 512 by decide)
    have hSplit := Nat.mod_add_div producer 512
    omega
  have hExit := exitedOfComplete hX hDone hThread
  obtain ⟨hCuQ,hUsedK⟩ := hFootprint.metadataProtected hp
  obtain ⟨pub,hPeer,_⟩ :=
    terminalFinalPeerOfActiveWait hp hX hCuQ hUsedK hActive hWait hPass hExit
  obtain ⟨first,hFirst,hGeneration,_⟩ := terminalStoresOfFinalPeer hX hPeer
  have hPos : pub-2 = first := by omega
  exact ⟨pub,hDrain.publishedWords hp hX hPeer.publication hExit,hPos.symm ▸ hGeneration⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
