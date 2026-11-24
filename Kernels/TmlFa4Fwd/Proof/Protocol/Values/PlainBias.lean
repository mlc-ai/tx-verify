-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.PlainWindow
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.BiasColumn

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values

/-- All columns of a plain round are attended, with zero bias. -/
theorem soft_plain_bias {p L m g B t u col} (hp : Pre p L m) (hg : g<L.threads)
    (hw : Prologue.warpIndex L g<8) (rounds : StageRounds p L g B)
    (tile : tileOf p L (g/L.block) = some t)
    (valid : t.Valid p (Prologue.warpIndex L g/4) (rowIx L g))
    (hu : B<u) (hn : u<t.n) (hcol : col<128) :
    let row := t.rowOf (Prologue.warpIndex L g/4) (rowIx L g)
    let key := t.key u col
    key<p.keyCount t.batch row ∧ biasAt p t.batch t.head row key=0 := by
  obtain ⟨b,hb,lo,hi,bound⟩ := plain_window hp hg hw rounds hu
  obtain rfl := Option.some.inj (tile.symm.trans (tileOf_eq (tileOf_some tile).1 ⟨hb,lo,hi⟩))
  intro row key
  let st : Fin 2 := ⟨Prologue.warpIndex L g/4,by omega⟩
  let q : Fin 2 := ⟨col/64,by omega⟩
  have idx : 64*q.val+col%64 = col := by dsimp [q]; omega
  have bounds := bias_column_key (st := st) (q := q) hp hb hn (Nat.mod_lt col (by decide : 0<64))
    (Nat.mod_lt _ (by decide : 0<128)) valid
  obtain ⟨_,eq⟩ := bounds
  rw [Nat.add_assoc _ (64*q.val) _,idx] at eq
  have src := eq (.inr (by omega))
  change _ = p.biasColumn b row key at src
  have hleft : p.biasColumn b row key < 0 := by
    rw [← src]
    unfold Loader.biasOriginCol
    have h := bound hn
    have stage : st=0 ↔ Prologue.warpIndex L g/4=0 := Fin.ext_iff
    simp only [stage,decide_eq_true_eq] at *
    split_ifs at h ⊢ <;> have := q.isLt <;> omega
  refine ⟨attended_left valid hleft,?_⟩
  change biasAt p b _ row key = 0
  simp only [biasAt,not_le.mpr hleft,false_and,ite_false]

end PTX.Kernels.TmlFa4Fwd.Proof.Values
