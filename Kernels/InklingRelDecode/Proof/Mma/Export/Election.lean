-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Lemmas.Flow.ElectLead
import Kernels.InklingRelDecode.Proof.Mma.Machine
import Kernels.InklingRelDecode.Proof.Common.History
import Kernels.InklingRelDecode.Proof.Mma.Facts.Election

namespace PTX.Kernels.InklingRelDecode.Proof.Mma.Export
open PTX PTX.Flow

private def sites :=
  [2499,2546,2548,2553] ++ (List.finRange 8).map qkPc ++ (List.finRange 8).map pvPc

private theorem won_site (s : Site) (h : s.pc ∈ sites) : s.won = true := by
  cases s <;> first | rfl | exact absurd h (by decide +kernel)

private theorem core {Q L m X g k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k) = some e) (hu : ∀ f, e.kind ≠ .ub f) (pc : e.pc ∈ sites) :
    Elected ((X.tr g).take k) (laneOf L g) := by
  have range : ∀ pc ∈ sites, 2422 < pc ∧ pc < 2557 := by decide +kernel
  obtain ⟨w,x,r,d,n,hs,hd⟩ := mma_state hp hX hf he hu (range _ pc).1 (range _ pc).2
  let I := fun (s : D) (nm : Cls → Nat) => s.site.won = true → 0 < nm (.winner (laneOf L g))
  have hh := mma_history hp hX hf (Frame.lt_of_get hX he) I
    (fun _ => fun h => by cases h) (fun s n e s' _ h hn hw => by
      rcases predecessor_won hn hw with hold | ⟨mask,inst,hwin⟩
      · exact Nat.lt_of_lt_of_le (h hold) (Nat.le_add_right ..)
      · simp only [Code.bump,cls,hwin,beq_self_eq_true,↓reduceIte]
        omega) (Frame.noUbBefore_of_get hX he) hs
  exact elected_of_count hs (hh (won_site _ (hd ▸ pc)))

/-- Every ordinary event at a winning Mma instruction has a prior election of its lane. -/
public theorem elected {Q L m X g k e} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k) = some e) (hu : ∀ f, e.kind ≠ .ub f)
    (pc : e.pc ∈ [2499,2546,2548,2553]) :
    Elected ((X.tr g).take k) (laneOf L g) :=
  core hp hX hf he hu (by simp only [sites,List.mem_append]; exact .inl (.inl pc))

/-- The QK and PV issues are winner-only too: the issuing lane was elected before. -/
public theorem elected_issue {Q L m X g k pc dst s acc mask} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (he : X.get (g,k) = some ⟨pc,.tc (.mma dst s acc mask)⟩)
    (issue : pc ∈ [2483,2486,2488,2490,2492,2494,2496,2498,
      2530,2533,2535,2537,2539,2541,2543,2545]) :
    Elected ((X.tr g).take k) (laneOf L g) :=
  core hp hX hf he (fun _ => nofun)
    (by
      have all : ∀ p ∈ [2483,2486,2488,2490,2492,2494,2496,2498,
          2530,2533,2535,2537,2539,2541,2543,2545], p ∈ sites := by decide +kernel
      exact all _ issue)

end PTX.Kernels.InklingRelDecode.Proof.Mma.Export
