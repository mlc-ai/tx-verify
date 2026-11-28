-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Mbar.ScalarReach
public import Lemmas.Protocol.ObservedSync
import Kernels.InklingRelDecode.Proof.Protocol.KV.Decl
import Lemmas.Protocol.ReachJoint

@[expose] public section

/-! # The unit handoff of a probability slot

Lane zero's publication on a slot is observed by the elected MMA lane's poll: the handoff from the
one producer to the one consumer, from the reuse paths (`Scalar.goals_all`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar
open PTX PTX.Flow PTX.MbarRing MbarRow

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The probability slot's handoff from lane zero to the elected MMA lane.** -/
public theorem prob_handoff (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (rows : MbarRows Q L X) (init : Mbar.InitRows L X)
    (words : RoleBytes L X) {c : Nat} (hc : c < L.grid) (s : Fin 2) :
    UnitHandoff L X ((Object.prob s).loc L c) (fun g => ∃ _ : Fin 1, g = c*L.block)
      (fun h => h = KV.leader L X c 7) 0 := by
  obtain ⟨hy,cy,wy⟩ := KV.leader_warp (X := X) hp hc (by decide : 7<8)
  have hz : c*L.block < L.threads := by simp only [Launch.threads,hp.block] at *; omega
  have cz : c*L.block/L.block = c := by simp [hp.block]
  refine Unit.Obj.handoff hX (probability hX rows init (c := c) s)
    (cons := fun h => h = KV.leader L X c 7) ?_ ?_ ?_
  · rintro h rfl
    exact Reach.unit_reach hX (probability hX rows init (c := c) s)
      (fun n hn => (goals_all hp hX hf rows init words c hc n hn).1 s)
  · intro h j pc p acq sc hh get
    subst hh
    rcases prob_use rows hy get rfl with kd|⟨q,ok,kd⟩|⟨-,kd⟩
    · cases kd
    · obtain ⟨-,-,-,h,-⟩ := Kind.wait.inj kd
      exact h
    · cases kd
  · intro a h i j pc pc' p acq sc sc' hh geta getw
    subst hh
    have lw := Frame.lt_of_get hX getw
    rcases prob_use rows hz geta rfl with kd|⟨q,ok,kd⟩|⟨-,kd⟩
    · cases kd
    · cases kd
    rcases prob_use rows lw getw rfl with kd'|⟨q,ok,kd'⟩|⟨-,kd'⟩
    · cases kd'
    · obtain ⟨-,-,-,-,rfl⟩ := Kind.wait.inj kd'
      obtain ⟨-,-,-,-,rfl⟩ := Kind.arrive.inj kd
      exact ⟨⟨hz,lw,by rw [cz,cy]⟩,lw,hz,by rw [cz,cy]⟩
    · cases kd'

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Scalar
