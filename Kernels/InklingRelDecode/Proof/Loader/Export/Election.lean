-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Flow.ElectLead
import Kernels.InklingRelDecode.Proof.Common.History
import Kernels.InklingRelDecode.Proof.Loader.Facts.Election

namespace PTX.Kernels.InklingRelDecode.Proof.Loader.Export
open PTX PTX.Flow

private def sites := [2389,2391,2394,2396,2404,2406,2410,2412]

private theorem won_site (s : Site) (h : s.pc ∈ sites) : s.won = true := by
  cases s <;> first | rfl | exact absurd h (by decide) |
    (rename_i p; fin_cases p <;> exact absurd h (by decide))

/-- Every ordinary event at a winning Loader instruction has a prior election of its lane. -/
public theorem elected {Q L m X g k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k) = some e) (hu : ∀ f, e.kind ≠ .ub f)
    (pc : e.pc ∈ [2389,2391,2394,2396,2404,2406,2410,2412]) :
    Elected ((X.tr g).take k) (laneOf L g) := by
  have range : ∀ pc ∈ sites, 2344 < pc ∧ pc < 2422 := by decide
  obtain ⟨w,x,r,d,n,hs,hd⟩ := loader_state hp hX hf he hu (range _ pc).1 (range _ pc).2
  let I := fun (s : D) (nm : Cls → Nat) => s.site.won = true → 0 < nm (.winner (laneOf L g))
  have hh := loader_history hp hX hf (Frame.lt_of_get hX he) I
    (fun _ => fun h => by cases h) (fun s n e s' _ h hn hw => by
      rcases predecessor_won hn hw with hold | ⟨mask,inst,hwin⟩
      · exact Nat.lt_of_lt_of_le (h hold) (Nat.le_add_right ..)
      · simp only [Code.bump,cls,hwin,beq_self_eq_true,↓reduceIte]
        omega) (Frame.noUbBefore_of_get hX he) hs
  exact elected_of_count hs (hh (won_site _ (hd ▸ pc)))

end PTX.Kernels.InklingRelDecode.Proof.Loader.Export
