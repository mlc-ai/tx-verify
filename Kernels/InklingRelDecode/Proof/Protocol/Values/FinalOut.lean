-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.PvClosed
public import Kernels.InklingRelDecode.Proof.Protocol.Values.LdeReal
import Kernels.InklingRelDecode.Proof.Mma.Export.BlockCommits

@[expose] public section

/-! # The epilogue's load returns the accumulator of the fold

The word is the real of the last PV step of the last ordinal (`ld_e_real`), the closed form of
its row and column after the CTA's blocks (`pv_closed_form`), which is the `o` of the row's
fold (`closedAcc_eq`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.TcMma PTX.Kernels.InklingRelDecode.Proof Tmem Lib.SoftRow

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The word of the epilogue's load of a valid row is the `o` of the row's fold.** The row is
the tile row of the cell's lane, the dimension its column in the accumulator. -/
theorem final_out (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (hu : NoUbOutside L X) (safe : ¬Race L X) (hG : SyncGuarded L kernel X)
    (base : ∀ {g k a bs}, X.get (g, k) = some ⟨13, .rd a bs⟩ →
      a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 →
      bs = (PTX.Proof.b32 0).toBytes.map some)
    (rows : MbarRows Q L X) (init : Protocol.Mbar.InitRows L X) (hws : WritesSafe L X)
    (ht : Tmem.One.Tmem1Facts L X 0) (hmd : Tmem.AccessCp.AsyncDoneDealloc L X)
    (words : RoleBytes L X) (nub : ¬ Assumptions.inputReadOnly.ub L m X)
    (form : Iface.KvCopyForm Q L X) (W : Iface.PWords X)
    {pw : Nat → Nat → Nat → Nat → ℝ} {al : Nat → Nat → Nat → ℝ} (P : PWords Q L X pw)
    (hR : ∀ {src a vals sh}, X.get src = some ⟨2328, .tc (.st a vals sh)⟩ →
      ∀ v ∈ vals, ∃ r : ℝ, v = .float .f32 r)
    (tie : RescaleLd X) (ord : LdBeforeSt X) (RA : RescaleAl Q L X al) (NR : NoRescaleAl Q L X al)
    (RB : RescaleBound Q L X) (F : FoldWords Q L pw al) (hs : 0 < Q.scale)
    {t k0 a vals sh j} (he : X.get (t, k0) = some ⟨2607, .tc (.ld a vals sh)⟩)
    (hj : j < vals.length)
    (valid : Lib.QRowValid Q L (t / L.block) (laneRow (tcDataCell L t sh a j).lane)) :
    vals[j]? = some (.float .f32 (rowState Q (ctaZ L (t / L.block)) (ctaXc L (t / L.block))
      (laneRow (tcDataCell L t sh a j).lane / 6)
      (ctaY L (t / L.block) * 6 + laneRow (tcDataCell L t sh a j).lane % 6)
      ((tcDataCell L t sh a j).column - 256)).o) := by
  obtain ⟨g, kR, r1, cy, pat, ordN, rr, hv⟩ := ld_e_real hp hX hf hu safe hG base rows init hws ht
    hmd words nub form W P hR RB he hj valid
  obtain ⟨d7, s7, a7, m7, gw⟩ := pat
  obtain ⟨b, -, pb, hb1, -⟩ := Mma.Export.pv_block hp hX hf base gw ⟨7, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, Lib.blocksOf Q L (t / L.block) = n + 1 :=
    ⟨Lib.blocksOf Q L (t / L.block) - 1, by omega⟩
  obtain ⟨row, col, hrow, hcol, hcell, hcl⟩ := pv_closed_form hp hX hf hu safe hG base rows init
    hws ht hmd words nub form W P hR tie ord RA NR n ⟨d7, s7, a7, m7, gw⟩
    (by omega) (by rw [cy]; omega) rr
  have e1 : laneRow (tcDataCell L t sh a j).lane = row := by
    rw [hcell]
    show 16 * ((32 * (row / 16) + row % 16) / 32) + (32 * (row / 16) + row % 16) % 32 = row
    omega
  have e2 : (tcDataCell L t sh a j).column - 256 = col := by
    rw [hcell]
    show 256 + col - 256 = col
    omega
  rw [e1] at valid ⊢
  rw [e2, hv, hcl (cy ▸ valid), cy]
  have hn' : Q.numIters (ctaZ L (t / L.block)) (ctaXc L (t / L.block)) = n + 1 := hn
  have hk := closedAcc_eq F valid col (n + 1)
  rw [hk, ← hn', ← kState_eq, rowState_eq Q hs]
  rfl

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
