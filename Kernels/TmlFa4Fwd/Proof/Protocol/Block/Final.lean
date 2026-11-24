-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Block.Channels
public import Kernels.TmlFa4Fwd.Proof.Top.Register
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Init
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.InitOne
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.Start
import Kernels.TmlFa4Fwd.Proof.Protocol.Ready.Obj
import Kernels.TmlFa4Fwd.Proof.Top.Prog.Entry
import Lemmas.Protocol.UnitReachBlocker
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # A barrier of a lane's CTA has a final state

A lane past its role's entry is past the startup's CTA barrier, so the startup's initializations of
the CTA's barriers are recorded (`final_exists`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

theorem final_exists (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hg : g < L.threads) {i : Role} {d : (frag p L g i).D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread p L) X g (X.tr g).length = some (some (.inr ⟨i, d⟩, n)))
    (hE : ¬ IsEntry i d) {o c : Nat} (ho : ObjOff o)
    (hinit : PairTmaRing.InitFirst X (obj L g o) c) : ∃ f, Final X (obj L g o) f := by
  have hT := table_shape_of hp hFw
  have hF := table_followed hp hX hFw
  obtain ⟨j, hj, i', n', hj'⟩ := Top.first_role _ _ _ hσ
  have hlt : j < (X.tr g).length := by
    rcases Nat.lt_or_eq_of_le hj with h | h
    · exact h
    · exfalso
      subst h
      rw [hσ] at hj'
      simp only [Option.some.injEq, Prod.mk.injEq, Sum.inr.injEq] at hj'
      obtain ⟨h1, -⟩ := hj'
      cases h1
      exact hE (by cases i <;> first | rfl | trivial)
  have hb0 := role_bar0 hp hX _ hj'
  obtain ⟨e, c', hin, -⟩ := init_exists hp hX hT hF hg hlt hb0 ho
  obtain ⟨i0, r0, hi, -⟩ := init_record_of_consistent hX hin
  exact MbarRing.Unit.final_of_init hX hinit
    (AsyncCopy.objects_noInval hX.tma.2.2.1 (no_inval hp hX hFw) _)
    (fun h0 => by rw [h0] at hi; simp at hi)

end
end PTX.Kernels.TmlFa4Fwd.Proof
