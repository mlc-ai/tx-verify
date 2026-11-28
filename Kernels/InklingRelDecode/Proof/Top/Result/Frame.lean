-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Protocol.Shared.GlobalWrites
import Kernels.InklingRelDecode.Proof.Protocol.Shared.GlobalInject
import Kernels.InklingRelDecode.Proof.Lib.Geometry
import Kernels.InklingRelDecode.Proof.Lib.Coordinates
import Kernels.InklingRelDecode.Proof.Lib.Rows
import Lemmas.Kernel.Memory

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Top
open PTX

/-- **Every output-site store lies in the `OPart` or the `LsePart` array**, from the exact
location `store_address` gives. -/
theorem Result.output_placed {Q L m X} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) :
    Protocol.Shared.OutputPlaced Q X := by
  intro ⟨g, k⟩ pc a bs he site l cov _
  have hsite : Protocol.Shared.IsStoreSite pc := by
    simp only [Protocol.Shared.outputSites, List.mem_cons, List.mem_map, List.mem_range] at site
    rcases site with rfl | ⟨j, hj, rfl⟩
    · exact .inl rfl
    · exact .inr ⟨⟨j, hj⟩, rfl⟩
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, vt, sz, loc⟩ := Export.store_address hp hX hf he hsite
  have bx := (Lib.coordinate_bounds hp hg).1
  have tn := Lib.token_lt hp (Lib.coordinate_bounds hp hg).2.2 vt
  obtain ⟨_, _, hl3, hl4⟩ := cov
  rcases loc with ⟨j, _, hloc⟩ | ⟨_, _, hloc⟩ <;> rw [hloc] at hl3 hl4
  · have r := Lib.oLoc_range (Q := Q) _ _ ((L.ctaidOf (g/L.block)).get .y * 6 +
      Lib.rowM (g % L.block) % 6) (64 * (g % L.block / 16 % 2) + j.val) bx tn
      (by have := Lib.rowM_lt (g % L.block); have := (Lib.coordinate_bounds hp hg).2.1
          simp only [heads, kvHeads] at *; omega)
      (by have := j.isLt; simp only [headDim]; omega)
    simp only [oLoc, sz] at hl3 hl4 r
    exact .inl (by omega)
  · have r := Lib.lseLoc_range (Q := Q) _ _ ((L.ctaidOf (g/L.block)).get .y * 6 +
      Lib.rowM (g % L.block) % 6) bx tn
      (by have := Lib.rowM_lt (g % L.block); have := (Lib.coordinate_bounds hp hg).2.1
          simp only [heads, kvHeads] at *; omega)
    simp only [lseLoc, sz] at hl3 hl4 r
    exact .inr (by omega)

theorem Result.frame {Q L mem0 X m} (hp : Pre Q L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (fin : IsFinal L mem0 X m) (placed : Protocol.Shared.OutputPlaced Q X) :
    ∀ l, l.space = .global →
    ¬ (Q.oBase ≤ l.addr ∧ l.addr < Q.oBase + oBytes Q) →
    ¬ (Q.lseBase ≤ l.addr ∧ l.addr < Q.lseBase + lseBytes Q) → m l = mem0 l := by
  intro l global outsideO outsideLse
  apply fin.unwritten
  intro ref a bs write cover
  exact (Protocol.Shared.output_intent hp hX placed write.intent cover global).elim
    outsideO outsideLse

end PTX.Kernels.InklingRelDecode.Proof.Top
