-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Count
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.TileAgree
public import Kernels.TmlFa4Fwd.Proof.Lib.OutputFrame
import Kernels.TmlFa4Fwd.Proof.Lib.RowBias
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Select
import Lemmas.Flow.Arith32WordW

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX.Flow.Arith32

/-- The mask computation uses the picked request lengths and the unshifted tile row. -/
theorem mask_words {p L m g} (hp : Pre p L m) (hg : g<L.threads)
    {d : D} {ns nv} (hF : SmWarp.SFits p L g d ns nv)
    (hep : SmWarp.epi d.site = .ready 0) (huk : d.site.hasUk = true) :
    ∃ b < p.batch, tilePrefix p b*p.heads ≤ g/L.block ∧ g/L.block < tilePrefix p (b+1)*p.heads ∧
      d.v.sc.c0 = W (p.qOffset b) ∧ d.v.sc.c1 = W (p.qOffset (b+1)) ∧ d.v.ukw = W (p.kLength b) ∧
      shl (rowOff p L g d.v.sc) 8 = W (256*(Epilogue.assignedCoordinates p b (g/L.block)).1) := by
  obtain ⟨fit,uk⟩ := hF
  simp only [Epilogue.Fits,SmWarp.toE,hep] at fit
  obtain ⟨R,bal,hC,h0,h1⟩ := fit
  obtain ⟨b,hb,lo,hi,hch,co⟩ := Epilogue.chosen_spec hp hg hC
  change Epilogue.chosen d.v.sc = _ at hch
  have range := hp.shape.2.1
  have eu := uk huk
  rw [hch,Mma.ukv,r32_W (by omega),toNat_W (by omega)] at eu
  change d.v.sc.c0 = Epilogue.qv p (Epilogue.chosen d.v.sc) at h0
  change d.v.sc.c1 = Epilogue.qv p (addi (Epilogue.chosen d.v.sc) 1) at h1
  rw [hch,Epilogue.qv_W hp (by omega)] at h0
  rw [hch,show (1 : Int) = ((1 : Nat) : Int) from rfl,addi_W (by decide) (by omega),
    Epilogue.qv_W hp (by omega)] at h1
  refine ⟨b,hb,lo,hi,h0,h1,eu,?_⟩
  have rv := congrArg Epilogue.Coords.row co
  let v := d.v
  let a := (Mma.coords p L g v.sc).n2
  let b' := (Mma.coords p L g v.sc).d2
  change addi (shl (add32 v.sc.nt (not32 (fdiv a b'))) 8) 1073741824 = _ at rv
  have hrow := (Epilogue.assignedCoordinates_valid hp lo hi).1
  have hlen := (hp.lengths b hb).2
  rw [row_agree] at rv
  exact row_unbias (shl8_lt _) (by omega) rv

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
