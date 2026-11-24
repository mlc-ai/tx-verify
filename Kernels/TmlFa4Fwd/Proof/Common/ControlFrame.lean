-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Lemmas.Kernel.FrameU
import Kernels.TmlFa4Fwd.Proof.Common.Sound
public import Kernels.TmlFa4Fwd.Proof.Startup.Shape
import Lemmas.Kernel.Counted
import Lemmas.Kernel.UbLast

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

theorem countU {σ n} (hs : Frame.stateAt (thread p L) X g k = some (some (σ, n)))
    (c : Cls) : ((X.tr g).take k).countP (cls L g c) = n c :=
  (Frame.count_eq (C := fun g => Code.glue (Startup.code p L g) (frag p L g) (exit L g))
    (cls := fun g => cls L g) hs c).symm

theorem ub_zeroU (hX : Consistent L kernel Assumptions.all m X) {σ n e}
    (he : X.get (g, k) = some e)
    (hs : Frame.stateAt (thread p L) X g k = some (some (σ, n))) : n .ub = 0 := by
  by_contra h
  obtain ⟨j, hj, ⟨pc, kind⟩, hf, hc⟩ := Frame.exists_of_count
    (C := fun g => Code.glue (Startup.code p L g) (frag p L g) (exit L g))
    (cls := fun g => cls L g) hs (Nat.pos_of_ne_zero h)
  cases kind <;> simp [cls] at hc
  have := ub_last hX (show X.get (g, j) = some ⟨pc, .ub _⟩ from hf) he
  omega

theorem start_firedU (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    {e : Event} {s : Startup.D} {n : Cls → Nat} (he : X.get (g, k) = some e)
    (hs : Frame.stateAt (thread p L) X g k = some (some (.inl s, n)))
    (hu : ∀ f, e.kind ≠ .ub f) : Startup.Ev L g s e ∧ exit L g s = none ∧ e.pc = s.site.pc := by
  obtain ⟨_, _, _, hat, ⟨hi, hx⟩, hc, hf⟩ :=
    Frame.fired_siteU (fun _ hg => thread_sound hp hg) hX he hs hu
  exact ⟨Startup.shape hp hat hi hc hf, hx, EventFrame.fires_source_pc hf⟩

end PTX.Kernels.TmlFa4Fwd.Proof
