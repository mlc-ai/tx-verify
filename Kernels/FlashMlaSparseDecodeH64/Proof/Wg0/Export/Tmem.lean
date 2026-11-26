-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.TmemRows.Wg0
public import Lemmas.Tmem.PairProtocol
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmemCnt

@[expose] public section

/-! # Warpgroup 0's `tcgen05` events

`tmemRow_wg0`: a `tcgen05` event of warpgroup 0 is a fence, a wait, a `32x32b` load at column
`400 + 32 k` or `64 c`, a store at column `64 c`, or the deallocation at pc 1840 (the shape table
`Wg0/Ev.lean`, through `wg0_at`). `wg0_deallocOps`: the deallocation is warp 0's, frees column
0 and 512 columns (the moved constants of pcs 1838–1839, in the shape table), as the thread's
third paired operation (the ledger's count `Wg0.TmemAt`); `wg0_exitOps`: a lane of warp 0 exits
after three. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **Row `TmemRow.Wg0`**. -/
theorem tmemRow_wg0 (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) : TmemRow.Wg0 P L X := by
  intro g k e c _ he hat hk
  obtain ⟨-, hr⟩ := hat
  obtain ⟨d, -, ⟨hpc, hE⟩, -⟩ := wg0_at hp hX hFw he (fun _ h => by rw [hk] at h; cases h) hr
  obtain ⟨s, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  unfold TmemRow.Wg0Tc
  cases s <;> simp [Wg0.EvK, Wg0.TcLdEv, Wg0.TcStEv, GWrAt, RdAt, WrAt, GenWrAt, Wg0.NcEv,
    Wg0.PollEv, Wg0.ArrEv, hk] at hE
  case tcfa | rsf | efa => subst hE; exact .inl hk
  case tcfb | rsfb => subst hE; exact .inr (.inl hk)
  case sldw | rldw | oldw => subst hE; exact .inr (.inr (.inl hk))
  case rstw => subst hE; exact .inr (.inr (.inr (.inl hk)))
  case sld kk =>
    obtain ⟨vals, rfl⟩ := hE; exact .inr (.inr (.inr (.inr (.inl ⟨kk, vals, hk⟩))))
  case rld cc | old cc =>
    obtain ⟨vals, rfl⟩ := hE; exact .inr (.inr (.inr (.inr (.inr (.inl ⟨cc, vals, hk⟩)))))
  case rst cc =>
    obtain ⟨vals, rfl⟩ := hE
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨cc, vals, hk⟩))))))
  case dealloc =>
    obtain rfl := hE
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨hpc, _, _, hk⟩))))))

variable {g k : Nat} {e : Event}

/-- **Warpgroup 0's deallocation**: warp 0's, of column 0 and 512 columns, its thread's third
paired operation. -/
theorem wg0_deallocOps (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) (he : X.get (g, k) = some e) (hat : MbarRow.Wg0At L g e.pc)
    {grp : CtaGroup} {dst : Option Loc} {act : Tmem.Request}
    (hk : e.kind = .tc (.resource grp dst act)) :
    MbarRow.warp L g = 0 ∧ act = .dealloc 0 512 ∧ Tmem.Pair.tmemOps ((X.tr g).take k) = 2 := by
  obtain ⟨-, hr⟩ := hat
  obtain ⟨d, hT, hE⟩ := wg0_tmem hp hX hFw he (fun _ h => by rw [hk] at h; cases h) hr
  have hs := Wg0.tmemOp_site hE (by simp [Tmem.Pair.isTmemOp, hk])
  simp only [Wg0.TmemAt, hs, ↓reduceIte] at hT
  obtain ⟨h0, h2⟩ := hT
  obtain ⟨-, hE⟩ := hE
  simp only [Wg0.EvK, hs, hk, Kind.tc.injEq, TcKind.resource.injEq, reduceCtorEq,
    exists_false, or_false] at hE
  exact ⟨(warpW_zero hp).1 h0, hE.2.2, h2⟩

/-- **A lane of warp 0 exits after its three paired operations.** -/
theorem wg0_exitOps (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {pc : Nat} (he : X.get (g, k) = some ⟨pc, .exit⟩)
    (hw : MbarRow.warp L g = 0) : Tmem.Pair.tmemOps ((X.tr g).take k) = 3 :=
  exit_tmem hp hX hFw he hw

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
