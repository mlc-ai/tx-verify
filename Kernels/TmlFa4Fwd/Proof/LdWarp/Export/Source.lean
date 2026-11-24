-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Open
public import Kernels.TmlFa4Fwd.Proof.Lib.Export
import Kernels.TmlFa4Fwd.Proof.LdWarp.AddrRecv
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.Local
import Kernels.TmlFa4Fwd.Proof.LdWarp.Open
import Kernels.TmlFa4Fwd.Proof.LdWarp.RowAddr
import Kernels.TmlFa4Fwd.Proof.Lib.GlobalWrites
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.CpCount
import Kernels.TmlFa4Fwd.Proof.Loader.Mem.CpOk
import Kernels.TmlFa4Fwd.Proof.Startup.Export.Mem
import Lemmas.Flow.WordBound

@[expose] public section

/-! # The sources of the loader's row copies

A row copy reads, inside the 256 bytes of a K or V row of the cache, the 16 bytes of the lane's
column of the row's half (`ld_cp_src`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX.Kernels.TmlFa4Fwd.Proof.LdWarp (RowA Halves)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat}

private theorem off_words : ∀ i < 512,
    (wideU2 (andi (shl (BitVec.ofNat 64 i) 3) 56)).toNat = 16 * (i % 8) ∧
      (and64 (zext (shl (BitVec.ofNat 64 i) 4)) 112).toNat = 16 * (i % 8) := by
  decide +kernel

/-- The source word of a row copy: the row's address and the lane's column. -/
private theorem cp_ad (hp : Pre p L m) (w : Nat) (per : Per) (b : Bool) (i : Fin 16) (c : Fin 2)
    (v : V) (kk : Fin 2) : ∃ off : BitVec 64, off.toNat = 16 * (g % L.block % 8) ∧
      rv p L g w ⟨.cp per b i c, v, kk⟩ ((pkRegs (pk per b)).ad.getD i.val 0) =
        add64 (v.x0 ||| v.x1 <<< 32) off := by
  have hi : g % L.block < 512 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
  obtain ⟨h1, h2⟩ := off_words _ hi
  cases per <;> cases b
  case warm.true => exact ⟨_, h2, by fin_cases i <;> rfl⟩
  all_goals exact ⟨_, h1, by fin_cases i <;> rfl⟩

private theorem pair_val {x0 x1 : BitVec 64} {y : Nat} (h0 : x0.toNat = y % 2 ^ 32)
    (h1 : x1.toNat = y / 2 ^ 32) (hy : y < 2 ^ 64) : (x0 ||| x1 <<< 32).toNat = y := by
  have h : (x1 <<< 32).toNat = y / 2 ^ 32 * 2 ^ 32 := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, h1]
    omega
  rw [BitVec.toNat_or, h, h0, Nat.or_comm, Nat.mul_comm,
    ← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (by decide))]
  omega

/-- **The source of a row copy.** -/
theorem ld_cp_src (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L g = 14 ∨ Prologue.warpIndex L g = 15) {pc : Nat}
    {sp : AsyncCopy.Spec} (he : X.get (g, k) = some ⟨pc, .copy sp⟩) :
    ∃ lay, (lay = p.kLayout ∨ lay = p.vLayout) ∧ ∃ page < p.pages, ∃ h < p.kvHeads, ∃ r < 16,
      ∃ c < 2, ∃ t < 8, sp.src.loc = ⟨.global, 0, lay.base + 2 * (page * lay.pageStride +
        h * lay.headStride + r * lay.rowStride) + 16 * t + 128 * c⟩ ∧ sp.src.size ≤ 16 := by
  have hg := Frame.lt_of_get hX he
  have hub : ∀ f, (⟨pc, .copy sp⟩ : Event).kind ≠ .ub f := fun f h => by cases h
  rcases LdWarp.open_ev hp hX hFw hw he hub with ⟨s', n', -, -, -, hi, hev'⟩ |
    ⟨b, d, n, hσ, h0, hR, -, hev⟩
  · exact (start_mem hev' hi.2 trivial).elim
  obtain ⟨a1, -, -, -⟩ := Loader.copy_site hev hub
  have hcpsite : d.site.isCp = true := by rw [← a1]; rfl
  obtain ⟨per, v, i, j, hs⟩ : ∃ per v i j, d.site = .cp per v i j := by
    revert hcpsite
    cases d.site <;> simp [Loader.Site.isCp]
  have hrc := LdWarp.recv_ok hp hX hg hw k (List.getElem?_eq_some_iff.mp he).1.le b d n hσ h0
  obtain ⟨site, v', k2⟩ := d
  simp only at hs
  subst hs
  obtain ⟨y, ⟨lay, hl, page, hpg, h, hh, r, hr, hy⟩, hx0, hx1⟩ := hrc.1
  have hroom := LdWarp.row_room hp hl hpg hh hr
  have hpair := pair_val hx0 hx1 y.isLt
  obtain ⟨off, hoff, had⟩ := cp_ad (g := g) hp (Loader.wOf b) per v i j v' k2
  have hj := j.isLt
  simp only [Loader.Ev] at hev
  rcases hev with ⟨n', hk⟩ | ⟨f, hk⟩
  swap
  · cases hk
  have hsz := (actualCopyShape hX ⟨pc, he⟩).srcSize
  rw [(actualCopyShape hX ⟨pc, he⟩).widthEq] at hsz
  simp only [Kind.copy.injEq] at hk
  subst hk
  refine ⟨lay, hl, page, hpg, h, hh, r, hr, j.val, j.isLt, g % L.block % 8,
    Nat.mod_lt _ (by decide), ?_, hsz⟩
  simp only [Loc.mk.injEq, true_and]
  rw [had]
  have h3 : (add64 (v'.x0 ||| v'.x1 <<< 32) off).toNat = y.toNat + 16 * (g % L.block % 8) := by
    simp only [add64, r64, LdWarp.toNat_tb64, BitVec.toNat_add, hpair, hoff]
    omega
  rw [BitVec.toNat_add, h3, hy]
  have hcp : (BitVec.ofInt 64 (cpOff j)).toNat = 128 * j.val := by
    fin_cases j <;> decide
  rw [hcp]
  omega

end
end PTX.Kernels.TmlFa4Fwd.Proof
