-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Lib.Export
public import Kernels.TmlFa4Fwd.Proof.Startup.Shape
import Kernels.TmlFa4Fwd.Proof.Epilogue.Open
import Kernels.TmlFa4Fwd.Proof.Epilogue.Shape
import Kernels.TmlFa4Fwd.Proof.LdWarp.Open
import Kernels.TmlFa4Fwd.Proof.Loader.Shape
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The output and loader warps have no `tcgen05` event -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

/-- The startup has no `tcgen05` event. -/
theorem start_tcFree {s : Startup.D} (hev : Startup.Ev L g s e) (hx : exit L g s = none) :
    isTcColl e = false := by
  obtain ⟨pc, kind⟩ := e
  obtain ⟨site, x1, x2, x3⟩ := s
  cases site with
  | sh j =>
    fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨_, _, hk⟩ := hev <;> subst hk <;> rfl
  | elect j =>
    simp only [Startup.Ev] at hev
    rcases hev with ⟨_, _, _, hk⟩ | ⟨f, hk⟩ <;> subst hk <;> rfl
  | init q =>
    simp only [Startup.Ev] at hev
    rcases hev with ⟨_, _, hk⟩ | ⟨f, hk⟩ <;> subst hk <;> rfl
  | fence => simp only [Startup.Ev] at hev; subst hev; rfl
  | bar => simp only [Startup.Ev] at hev; subst hev; rfl
  | enter r => simp [exit] at hx

private theorem epi_notc {d : Epilogue.D} (hev : Epilogue.Ev p L g d e) : isTcColl e = false := by
  obtain ⟨pc, kind⟩ := e
  obtain ⟨s, rest⟩ := d
  cases s <;> simp only [Epilogue.Ev] at hev
  case store => cases kind <;> simp_all [Epilogue.isStore, isTcColl]
  all_goals shape_destruct hev
  all_goals rfl

set_option maxHeartbeats 4000000 in
private theorem ld_notc {w : Nat} {d : Loader.D} (hev : Loader.Ev p L g w d e) :
    isTcColl e = false := by
  obtain ⟨s, v, kk⟩ := d
  cases s <;> simp only [Loader.Ev] at hev
  case word | down | up | total | vote | pre | tiles => exact epi_notc hev
  all_goals obtain ⟨pc, kind⟩ := e
  all_goals shape_destruct hev
  all_goals subst_vars
  all_goals rfl

/-- **The output and loader warps have no `tcgen05` event.** -/
theorem noTc_of_warp (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : 13 ≤ Prologue.warpIndex L g) (he : X.get (g, k) = some e) :
    isTcColl e = false := by
  by_cases hub : ∃ f, e.kind = .ub f
  · obtain ⟨f, hf⟩ := hub
    obtain ⟨pc, kd⟩ := e
    simp only at hf
    subst hf
    rfl
  push Not at hub
  have h16 := Prologue.warpIndex_lt hp g
  rcases Nat.lt_or_ge (Prologue.warpIndex L g) 14 with h1 | h1
  · rcases Epilogue.open_ev hp hX hFw (by omega) he hub with ⟨s, n, -, -, -, hi, hev⟩ |
      ⟨d, n, -, -, -, -, hev⟩
    · exact start_tcFree hev hi.2
    · exact epi_notc hev
  · rcases LdWarp.open_ev hp hX hFw (by omega) he hub with ⟨s, n, -, -, -, hi, hev⟩ |
      ⟨b, d, n, -, -, -, -, hev⟩
    · exact start_tcFree hev hi.2
    · exact ld_notc hev

end PTX.Kernels.TmlFa4Fwd.Proof
