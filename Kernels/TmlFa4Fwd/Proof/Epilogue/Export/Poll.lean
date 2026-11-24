-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Open
public import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.Lib.EvPc
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.SiteUse
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Sites
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Two lanes of the output warp polling at one position poll one barrier -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g h : Nat}

/-- An output lane's poll is the ready poll of a stage. -/
private theorem out_poll (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g = 13) {k pc par : Nat} {l : Loc}
    {ok acq : Bool} {sc : MbarScope} (he : X.get (g, k) = some ⟨pc, .wait l par ok acq sc⟩) :
    ∃ st, pc = (Epilogue.Site.ready st).pc ∧ l = Epilogue.readyLoc L g st := by
  rcases Epilogue.open_ev hp hX hFw hw he (fun f h => by cases h) with
    ⟨s, n, hσ, -, -, hi, hev⟩ | ⟨d, n, hσ, -, -, -, hev⟩
  · exfalso
    obtain ⟨c, hc⟩ := start_mbar (l := l) hev hi.2 rfl
    cases hc
  · have hpc := ev_pc hp hX he hσ
    rcases epi_site hev (l := l) rfl with ⟨st, hs, hl⟩ | ⟨st, hs, -⟩
    · exact ⟨st, by rw [← hs]; exact hpc, hl⟩
    · exfalso
      simp only [Epilogue.Ev, hs] at hev
      cases hev

/-- **Two lanes of the output warp polling at one position poll one barrier.** -/
theorem out_poll_same (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g = 13) (hs : SameWarp L g h)
    {k k' pc par par' : Nat} {l l' : Loc} {ok acq ok' acq' : Bool} {sc sc' : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait l par ok acq sc⟩)
    (he' : X.get (h, k') = some ⟨pc, .wait l' par' ok' acq' sc'⟩) : l = l' := by
  have hwe : Prologue.warpIndex L g = Prologue.warpIndex L h := hs.2
  obtain ⟨st, hpc, hl⟩ := out_poll hp hX hFw hw he
  obtain ⟨st', hpc', hl'⟩ := out_poll hp hX hFw (by omega) he'
  have key : ∀ a b : Fin 2, (Epilogue.Site.ready a).pc = (Epilogue.Site.ready b).pc → a = b := by
    decide
  have := key st st' (hpc.symm.trans hpc')
  rw [hl, hl', this]
  simp only [Epilogue.readyLoc, hs.1.2.2]

end
end PTX.Kernels.TmlFa4Fwd.Proof
