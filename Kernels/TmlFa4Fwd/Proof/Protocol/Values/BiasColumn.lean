-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.BiasElement
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.BiasGap
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Export.BiasGroup

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values

/-- For an attended key the bias issue's column is exactly the specification column.
The exceptional first issue of a short stage zero only contains un-attended keys. -/
theorem bias_column_key {p L m} {b t u x ρ : Nat} {st q : Fin 2}
    (hp : Pre p L m) (hb : b<p.batch) (hu : u<Loader.tileBlocks p b t)
    (hx : x<64) (hr : ρ<128) (hv : 256*t+128*st.val+ρ < p.qLength b) :
    let n := Loader.tileBlocks p b t
    let n0 := Loader.stageZeroBlocks p b t
    let row := 256*t+128*st.val+ρ
    let key := 128*(n-1-u)+64*q.val+x
    let col := Loader.biasOriginCol (decide (n0<n)) st q u + x
    col < 1280 ∧ (key < p.keyCount b row ∨ u≠0 →
      col = p.biasColumn b row key) := by
  obtain ⟨_,hle,_⟩ := hp.lengths b hb
  have hs := st.isLt
  have hq := q.isLt
  have stage : (256*t+128*st.val+ρ)/128 = 2*t+st.val := by omega
  dsimp only
  unfold Loader.biasOriginCol Loader.stageZeroBlocks Loader.tileBlocks
    Params.biasColumn Params.keyCount
  rw [stage]
  unfold Loader.tileBlocks at hu
  simp only [decide_eq_true_eq]
  by_cases sz : st=0
  · subst st
    simp only [Fin.val_zero,true_and,Nat.mul_zero,Nat.add_zero]
    push_cast
    split <;> constructor <;> omega
  · have st1 : st.val=1 := by omega
    simp only [sz,st1,and_false,false_and,ite_false,add_zero]
    push_cast
    constructor <;> omega

end PTX.Kernels.TmlFa4Fwd.Proof.Values
