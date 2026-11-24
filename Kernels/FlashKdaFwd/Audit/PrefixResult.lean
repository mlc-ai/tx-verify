-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.PrefixCases
import Kernels.FlashKdaFwd.Audit.PrefixFinal

namespace FlashKda.Prefix
open PTX
noncomputable section

/-- A certificate for the zero thread determines the final memory of the whole 32-thread launch. -/
theorem final_of_replay {n input output offsets expected fuel X mem final}
    (checked : (replay [readonly] (launch n input output) 0 input offsets fuel {}).map
      (fun r => storesMatch output expected r.val) = some true)
    (hx : Consistent (launch n input output) Decoded.kernel [readonly] mem X)
    (done : Complete (launch n input output) X) (init : initialized mem input offsets)
    (fin : IsFinal (launch n input output) mem X final) : finalBytes output expected mem final := by
  obtain ⟨⟨es, cert, matched⟩, _⟩ := verified_stores checked
  have root := global_trace hx done (by decide : 0 < 32) init cert
  rw [← root] at matched
  simp only [storesMatch, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at matched
  have other {g : Nat} (hg : g ≠ 0) {j e} (he : X.get (g,j) = some e) :
      e = ⟨172,.exit⟩ := by
    by_cases hin : g < 32
    · let lane : Fin 31 := ⟨g-1, by omega⟩
      have eq : lane.val+1 = g := by dsimp [lane]; omega
      have hcert := idle_lanes n input output offsets lane
      rw [eq] at hcert
      have trace := global_trace hx done hin init hcert
      have mem : e ∈ X.tr g := List.mem_iff_getElem?.mpr ⟨j,he⟩
      simpa [trace] using mem
    · have large : (launch n input output).threads ≤ g := Nat.le_of_not_lt hin
      have empty := hx.outside g large
      change (X.tr g)[j]? = _ at he
      simp [empty] at he
  apply final_of_stores fin _ _ matched.2
  · rintro ⟨g,j⟩ e he
    by_cases hg : g=0
    · subst g
      exact matched.1 _ (List.mem_iff_getElem?.mpr ⟨j,he⟩)
    · rw [other hg he]
      rfl
  · rintro ⟨g,j⟩ a bs ⟨pc,he⟩
    by_contra hn
    have impossible := other hn he
    cases impossible

/-- For every complete consistent execution in this family, the output array contains
the mathematical tile prefixes and every other byte retains its launch value. -/
theorem packed_final_memory {n : Nat} (hn : n ∈ [0,1,2,3,4,5,6,7,8,23]) {X mem final} :
    let lengths := lengthsFor n
    let L := launch lengths.length 2048 4096
    Consistent L Decoded.kernel [readonly] mem X → Complete L X →
    initialized mem 2048 (offsetsOf lengths) → IsFinal L mem X final →
    finalBytes 4096 (expectedOf lengths) mem final := by
  exact final_of_replay (control_paths n hn)

end
end FlashKda.Prefix
