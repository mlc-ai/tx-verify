-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.Export
import Kernels.TmlFa4Fwd.Proof.SmWarp.Counts
import Kernels.TmlFa4Fwd.Proof.Softmax.MbarSite
import Kernels.TmlFa4Fwd.Proof.Startup.Export.MbarSite
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The softmax warps' mbarrier uses

`soft_mbar_use`: every event of a softmax lane that names an mbarrier and is no initialization is a
unit release arrival on the stage's barrier at offset 96, 112 or 336, or a poll of the stage's
barrier at offset 80, 192 or 320, with the parity of the lane's successful polls of it (plus one on
the credit barrier, 192). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax (RefQ ptsOf passed before inBias inPlain)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {h k : Nat} {e : Event} {l : Loc}

/-- A poll of the credit barrier is one ahead: its first poll passes on the fresh barrier. -/
def softΔ (a : Nat) : Nat := if a = 192 then 1 else 0

/-- The poll points before each poll site, and in a biased and a plain round. -/
private theorem poll_tab (b : Bool) :
    ([Softmax.Site.wq, .ws .first, .ws .bias, .ws .plain, .wb false, .wb true, .pwend .first,
      .pwend .bias, .pwend .plain, .wend true, .wend false].map fun s =>
        (ptsOf b (.acquire (Softmax.pollOff s))).countP (before s)) =
      [0, 0, 1, 1, 0, 1, 1, 2, 2, 2, 0] ∧
    ([80, 192, 320].map fun a => ((ptsOf b (.acquire a)).countP inBias,
      (ptsOf b (.acquire a)).countP inPlain)) = [(1, 1), (1, 1), (1, 0)] := by
  cases b <;> decide +kernel

private theorem par_word (n : Nat) :
    (truncBits 32 (Epilogue.i32 ((n % 2 : Nat) : Int))).toNat % 2 = n % 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h] <;> decide

private theorem par_word0 : (truncBits 32 (Epilogue.i32 0)).toNat % 2 = 0 := by decide
private theorem par_word1 : (truncBits 32 (Epilogue.i32 1)).toNat % 2 = 1 := by decide

set_option maxHeartbeats 4000000 in
/-- **The parity of a softmax poll** is that of its reference count. -/
private theorem poll_par {d : Softmax.D} {c : Softmax.Cnt → Nat} {rb rp : Nat}
    (hQ : RefQ p L h d c rb rp) (hs : d.site.isPoll = true) :
    (truncBits 32 (Softmax.pollW d)).toNat % 2 =
      (c (.acquire (Softmax.pollOff d.site)) + softΔ (Softmax.pollOff d.site)) % 2 := by
  obtain ⟨t1, t2⟩ := poll_tab (Softmax.lz L h)
  simp only [List.map, List.cons.injEq, Prod.mk.injEq, and_true, Softmax.pollOff] at t1 t2
  have hc := hQ.cnt (.acquire (Softmax.pollOff d.site)) rfl
  rw [hc]
  have hpre := hQ.pre
  have hbias := hQ.bias
  have hplain := hQ.plain
  have haft := hQ.after
  have hno := hQ.noTile
  clear hc hQ
  obtain ⟨site, v, kk, acc⟩ := d
  dsimp only at *
  cases site <;> simp only [Softmax.Site.isPoll, Bool.false_eq_true] at hs
  case wq =>
    obtain ⟨rfl, rfl⟩ := hpre (by decide)
    simp only [Softmax.pollW, Softmax.pollOff, passed, t1, t2, softΔ, par_word1]
    simp
  case ws r =>
    cases r
    · obtain ⟨rfl, rfl⟩ := hpre (by decide)
      simp only [Softmax.pollW, Softmax.pollOff, passed, softΔ, par_word0]
      simp [t1]
    · obtain ⟨rfl, hp, -⟩ := hbias (by decide)
      simp only [Softmax.pollW, Softmax.pollOff, passed, softΔ, hp.1, par_word]
      simp [t1, t2]
    · obtain ⟨hp, -⟩ := hplain (by decide)
      simp only [Softmax.pollW, Softmax.pollOff, passed, softΔ, hp.1, par_word]
      simp [t1, t2]
  case wb b =>
    cases b
    · obtain ⟨rfl, rfl⟩ := hpre (by decide)
      simp only [Softmax.pollW, Softmax.pollOff, passed, softΔ, par_word0]
      simp [t1]
    · obtain ⟨rfl, hp, -⟩ := hbias (by decide)
      simp only [Softmax.pollW, Softmax.pollOff, passed, softΔ, hp.2.2, par_word]
      simp [t1, t2]
  case pwend r =>
    cases r
    · obtain ⟨rfl, rfl⟩ := hpre (by decide)
      simp only [Softmax.pollW, Softmax.pollOff, passed, softΔ, par_word0]
      simp [t1]
    · obtain ⟨rfl, hp, -⟩ := hbias (by decide)
      simp only [Softmax.pollW, Softmax.pollOff, passed, softΔ, hp.2.1, par_word]
      simp [t1, t2]; omega
    · obtain ⟨hp, -⟩ := hplain (by decide)
      simp only [Softmax.pollW, Softmax.pollOff, passed, softΔ, hp.2, par_word]
      simp [t1, t2]; omega
  case wend b =>
    cases b
    · obtain ⟨rfl, rfl⟩ := hpre (by decide)
      have hw := hno rfl
      simp only [Softmax.pollW, Softmax.pollOff, passed, softΔ, hw, par_word1]
      simp [t1]
    · have hw := haft (by decide)
      simp only [Softmax.pollW, Softmax.pollOff, passed, softΔ, hw, par_word]
      simp [t1, t2]; omega

/-- **Every mbarrier use of a softmax lane.** -/
theorem soft_mbar_use (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L h < 8) (he : X.get (h, k) = some e)
    (hm : MbarOf e l) (hni : ∀ c, e.kind ≠ .mbInit l c) :
    (∃ a, (a = 96 ∨ a = 112 ∨ a = 336) ∧ l = obj L h (8 * (Prologue.warpIndex L h / 4) + a) ∧
        e.kind = .arrive l 0 1 true .cta) ∨
      ∃ a ok, (a = 80 ∨ a = 192 ∨ a = 320) ∧ l = obj L h (8 * (Prologue.warpIndex L h / 4) + a) ∧
        e.kind = .wait l ((okPolls l ((X.tr h).take k) + softΔ a) % 2) ok true .cta := by
  have hub : ∀ f, e.kind ≠ .ub f := by
    obtain ⟨pc, kd⟩ := e
    rintro f rfl
    simp only [MbarOf] at hm
  rcases soft_counts hp hX hFw hw he hub with ⟨s, hev, hx⟩ | ⟨d, c, rb, rp, _, _, hQ, -, hev, hc⟩
  · exact absurd (start_mbar hev hx hm) (fun ⟨c, hc⟩ => hni c hc)
  rcases soft_mbar hev hm with ⟨hk, hl, hmem⟩ | ⟨par, ok, hk, hl, hmem⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    exact .inl ⟨_, by omega, hl.trans (soft_bl hw _), hk⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    refine .inr ⟨_, ok, by omega, hl.trans (soft_bl hw _), ?_⟩
    have hpar : par = (truncBits 32 (Softmax.pollW d)).toNat % 2 ∧ d.site.isPoll = true := by
      exact soft_poll_par hev hk
    rw [hk, hpar.1, poll_par hQ hpar.2, hl, soft_bl hw, soft_okPolls hw, hc _ rfl]

end
end PTX.Kernels.TmlFa4Fwd.Proof
