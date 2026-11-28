-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Sound
public import Kernels.InklingRelDecode.Proof.Startup.Shape
public import Lemmas.Kernel.Counted
public import Lemmas.Kernel.FrameU
public import Lemmas.Kernel.Safety.TableU

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX PTX.Proof PTX.Flow

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem fcount {k : Nat} {σ : (thread Q L g).D}
    (h : Frame.stateAt (thread Q L) X g k = some (some σ)) (c : Cls) :
    σ.2 c = ((X.tr g).take k).countP (cls c) :=
  Frame.count_eq (C := fun g => Code.glue (Startup.code Q L g)
      (Code.withStubs (frag Q L g) Startup.Entry.pc) (Code.gatedExit Startup.enterOf (sel L g)))
    (cls := fun _ => cls) h c

/-- A fault-free trace prefix has zero faults in the glued machine's ledger. -/
theorem prefix_ub_zero {k : Nat} {s : (thread Q L g).D}
    (hs : Frame.stateAt (thread Q L) X g k = some (some s)) (hu : Frame.NoUbBefore X g k) :
    s.2 .ub = 0 := by
  rw [fcount hs]
  apply List.countP_eq_zero.mpr
  intro e hm
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hm
  rw [List.length_take] at hj
  have hjk : j<k := by omega
  have get : X.get (g,j)=some (((X.tr g).take k)[j]) := by
    change (X.tr g)[j]?=_
    rw [← List.getElem?_take_of_lt hjk]
    exact List.getElem?_eq_getElem _
  have clear := hu j hjk _ get
  generalize ((X.tr g).take k)[j] = ev at *
  cases h : ev.kind <;> first | exact (clear _ h).elim | simp [cls,h]

theorem zero_before_bump {n : Cls → Nat} {ev : Event}
    (h : Code.bump cls n ev .ub=0) : n .ub=0 := Nat.eq_zero_of_add_eq_zero_right h

theorem enterOf_init : Startup.enterOf (Startup.init L g) = none := by
  unfold Startup.init; split <;> rfl

theorem start_ev (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {e : Event} {s : Startup.D} {n : Cls → Nat} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread Q L) X g k = some (some (.inl s, n)))
    (hu : ∀ f, e.kind ≠ .ub f) : Startup.Ev L g s e := by
  obtain ⟨_, _, _, hat, hi, hc, hf⟩ := Frame.fired_siteU
    (fun g hg => thread_sound hp hg) hX he hσ hu
  exact Startup.shape hp hat hi.1 hc hf hu

end PTX.Kernels.InklingRelDecode.Proof
