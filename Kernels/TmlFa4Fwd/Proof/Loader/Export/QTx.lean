-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Open
public import Kernels.TmlFa4Fwd.Proof.Loader.Shape
import Kernels.TmlFa4Fwd.Proof.Common.Inj
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The transaction bytes of the loader's TMA groups

Every arrival of a loader lane expects 32768 bytes (`ld_arr_tx`), those of its group's two copies
(`input_bytes`, `Protocol/Mbar/Input.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

private theorem ta_tx (w : Nat) (d : Loader.D) (hs : (∃ t, d.site = .ta t) ∨ d.site = .da) :
    (truncBits 32 (Loader.rv p L g w d (Loader.taRegs d.site).2.2)).toNat = 32768 := by
  obtain ⟨s, v, k⟩ := d
  rcases hs with ⟨t, rfl⟩ | rfl
  · fin_cases t <;> rfl
  · rfl

/-- **An arrival of a loader lane expects 32768 bytes.** -/
theorem ld_arr_tx (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15)
    {k pc tx cnt : Nat} {l : Loc} {rel : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .arrive l tx cnt rel sc⟩) : tx = 32768 := by
  rcases LdWarp.open_ev hp hX hFw hw he (fun f h => by cases h) with
    ⟨s, n, -, -, -, hi, hev⟩ | ⟨b, d, n, -, -, -, -, hev⟩
  · exfalso
    have hx : exit L g s = none := hi.2
    obtain ⟨site, x1, x2, x3⟩ := s
    cases site with
    | sh j => fin_cases j <;> simp [Startup.Ev] at hev
    | elect j => simp [Startup.Ev] at hev
    | init q => simp [Startup.Ev] at hev
    | fence => simp [Startup.Ev] at hev
    | bar => simp [Startup.Ev] at hev
    | enter r => simp [exit] at hx
  · obtain ⟨site, v, kk⟩ := d
    cases site
    case ta t =>
      simp only [Loader.Ev, Kind.arrive.injEq] at hev
      exact hev.2.1.trans (ta_tx _ _ (.inl ⟨t, rfl⟩))
    case da =>
      simp only [Loader.Ev, Kind.arrive.injEq] at hev
      exact hev.2.1.trans (ta_tx _ _ (.inr rfl))
    all_goals exfalso
    all_goals simp only [Loader.Ev, Epilogue.Ev, Loader.Site.toE] at hev
    all_goals simp at hev

end
end PTX.Kernels.TmlFa4Fwd.Proof
