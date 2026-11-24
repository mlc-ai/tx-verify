-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaModel
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpAlignment
public import Kernels.TmlFa4Fwd.Flow.Code.Part043
public import Kernels.TmlFa4Fwd.Flow.Code.Part048
public import Lemmas.Flow.TcTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- The warp relinquishes the allocation permit, joins the final barrier, then deallocates
the original 512-column allocation before branching to the common exit. -/
theorem tailResourceTrace {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g pos col : Nat} (hc : col < 2 ^ 32)
    {t : TState} (ht : At t 2763 [(1179, b32 col)])
    (hr : Run kernel Assumptions.all l g t ((X.tr g).drop pos) none) :
    X.get (g, pos) = some ⟨2763, .tc (.resource .one none .relinquish)⟩ ∧
      X.get (g, pos + 1) = some ⟨2764, .bar 2 (some 416) .sync⟩ ∧
      X.get (g, pos + 2) = some ⟨2766, .tc (.resource .one none (.dealloc col 512))⟩ ∧
      ∃ u, At u 3099 [(1179, b32 col)] ∧
        Run kernel Assumptions.all l g u ((X.tr g).drop (pos + 3)) none := by
  let a := next t
  let b := next a
  let c := next (setReg b 2682 (b32 512))
  let e := next c
  let u := { e with pc := 3099 }
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hA : At a 2764 [(1179, b32 col)] := ht.next
  have hB : At b 2765 [(1179, b32 col)] := hA.next
  have hC : At c 2766 [(2682, b32 512), (1179, b32 col)] :=
    hB.set (by intro pair h; rcases List.mem_singleton.mp h with rfl; exact of_decide_eq_true rfl)
  have hE : At e 2767 [(2682, b32 512), (1179, b32 col)] := hC.next
  have hRel : out kernel Assumptions.all l g t =
      .ev (.tc (.resource .one none .relinquish) a) := by
    rw [out_eq_core (by rw [ht.1]; decide) (by rw [ht.1]; decide),
      out_event ht.2.2.2.1 (by rw [ht.1]; exact Flow.code_2763) rfl rfl]
    change Out.ev (tcTmpl l g t (.tcRelinquish .one)) = _
    simp [tcTmpl, hBlock, ofExec, a, pure, Except.pure]
  have hBar : out kernel Assumptions.all l g a = .ev (.bar 2 b (some 416) .sync) := by
    rw [out_eq_core (by rw [hA.1]; decide) (by rw [hA.1]; decide),
      out_event hA.2.2.2.1 (by rw [hA.1]; exact Flow.code_2764) rfl rfl]
    change Out.ev (barTmpl l g a (.imm 2) (some (.imm 416)) .sync) = _
    have hId : readBits l g a 32 (.imm 2) = .ok (BitVec.ofNat 64 2) := rfl
    have hN : readBits l g a 32 (.imm 416) = .ok (BitVec.ofNat 64 416) := rfl
    simp only [barTmpl, hId, hN, hp.block]
    rfl
  have hSet : run kernel [] l g 1 b = some c := by apply run_local Flow.code_2765 rfl hB; rfl
  have hSetA := localRun (by decide) (by decide) hB.1 rfl hSet
  have hDealloc : out kernel Assumptions.all l g c =
      .ev (.tc (.resource .one none (.dealloc col 512)) e) := by
    rw [out_eq_core (by rw [hC.1]; decide) (by rw [hC.1]; decide),
      out_event hC.2.2.2.1 (by rw [hC.1]; exact Flow.code_2766) rfl rfl]
    change Out.ev (tcTmpl l g c (.tcDealloc .one (.reg 1179) (.reg 2682))) = _
    have hCol := readBits_b32 (L := l) (g := g) hC.2.2.2.2.2.1 hc
    have hN := readBits_b32 (L := l) (g := g) hC.2.2.2.2.1 (by decide)
    have hCol64 : col < 2 ^ 64 := by omega
    simp [tcTmpl, hBlock, hCol, hN, Tmem.validColumns, ofExec, e,
      toNat_ofNat_lt hCol64, bind, Except.bind, pure, Except.pure]
  have hBranch : run kernel [] l g 1 e = some u := by
    apply run_local Flow.code_2767 rfl hE
    rw [execLocalA_nil]
    rfl
  have hBranchA := localRun (by decide) (by decide) hE.1 rfl hBranch
  have h₀ : Next kernel Assumptions.all l g t t (.tc (.resource .one none .relinquish) a) :=
    ⟨.refl, hRel⟩
  obtain ⟨_, v, he₀, ⟨rfl, hv⟩, hV⟩ := h₀.continuing_at (by rintro f ⟨_, h⟩; cases h) hr
  obtain rfl := Option.some.inj hv
  have h₁ : Next kernel Assumptions.all l g a a (.bar 2 b (some 416) .sync) := ⟨.refl, hBar⟩
  obtain ⟨_, v, he₁, ⟨rfl, hv⟩, hV⟩ := h₁.continuing_at (by rintro f ⟨_, h⟩; cases h) hV
  obtain rfl := Option.some.inj hv
  have h₂ : Next kernel Assumptions.all l g b c
      (.tc (.resource .one none (.dealloc col 512)) e) := ⟨run_rtg hSetA, hDealloc⟩
  obtain ⟨_, v, he₂, ⟨rfl, hv⟩, hV⟩ := h₂.continuing_at (by rintro f ⟨_, h⟩; cases h) hV
  obtain rfl := Option.some.inj hv
  refine ⟨by simpa only [ht.1] using he₀, by simpa only [hA.1] using he₁, ?_, u, ?_, ?_⟩
  · simpa only [hC.1, Nat.add_assoc] using he₂
  · exact ⟨rfl, hE.2.1, hE.2.2.1, hE.2.2.2.1, hE.2.2.2.2.2⟩
  · simpa only [Nat.add_assoc] using hV.after_local (run_rtg hBranchA)

end
end PTX.Kernels.TmlFa4Fwd.Mma
