-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Result.Writes
public import Lemmas.Kernel.IdenticalWrites
public import Lemmas.Tcgen05.MemFloat

@[expose] public section

/-! # The memory after a complete execution

Byte `z` of output element `(batch, head, row, d)` is written by slot `(x, y, z)` of the store
that the tile's store lane issued (`tile_store`), and every write of it is that slot of a store of
the same item, stage and half by a lane of the same CTA, with the same specification
(`output_writers`). Each such store writes byte `z` of the half-precision attention output there
(`StoreValues`), so the writes are writes of the same bytes with the same value
(`SameValueWrites`), and the final memory holds the tile store's byte
(`IsFinal.of_identical_writers`), and the element reads as the attention output
(`memFloat_float`). A global byte outside O has no writer (`frame`), so the final memory holds its
launch content (`post_of`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof

noncomputable section

namespace Result

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A work item is determined by its coordinates. -/
theorem work_eq {B H w w' : Nat} (h1 : w / B / H = w' / B / H) (h2 : w / B % H = w' / B % H)
    (h3 : w % B = w' % B) : w = w' := by
  have e1 := Nat.div_add_mod w B
  have e2 := Nat.div_add_mod w' B
  have e3 := Nat.div_add_mod (w / B) H
  have e4 := Nat.div_add_mod (w' / B) H
  rw [h1, h2, e4] at e3
  rw [← e3, h3, e2] at e1
  exact e1.symm

/-- **Every write of an output byte is the same slot of a store of the tile's item**: of the
same stage and half, with the same specification, by a thread of the same CTA. -/
theorem output_writers (hpre : Pre P L mem0) (hco : ItemCoords P L)
    (hX : Consistent L kernel asms mem0 X) (hs : StoreFacts P L X) (hw : WriteFacts L X)
    {g j x y z : Nat} {st hh : Fin 2} (hgt : g < L.threads) (hj : workOf L g j < totOf L)
    (hx : x < 64) (hy : y < 128) (hz : z < 2) :
    ∀ w a bs, X.MemWrites w a bs → a.Covers ((elementLoc P P.oBase P.sq (tileBatch L g j)
        (tileHead L g j) (tileRow L g j st + y) (64 * hh + x)).at z) →
      ∃ g' kk', w = storeWrite (g', kk') x y z ∧ g' < L.threads ∧ ctaOf L g' = ctaOf L g ∧
        X.get (g', kk') = some ⟨Store.Site.pc (.tma st hh),
          .tensorStore P.oMap (oSpec P L g' j st hh)⟩ ∧
        arrivals (freeBar L (ctaOf L g') st) ((X.tr g').take kk') = j := by
  intro w a bs hm hc
  have hgl : a.loc.space = .global := hc.1.symm
  obtain ⟨i', x', y', z', rfl⟩ := hw.global w a bs hm hgl
  obtain ⟨pc', j', st', hh', hgt', hget', hwarp', hsrc', hpc', harr', hj', hx', hy', hz', hsz,
    hloc⟩ := slot_write hpre hco hX hs hm
  rw [Acc.loc_of_one hc hsz] at hloc
  obtain ⟨hb, hhd, -⟩ := tile_lt hpre hco hj
  obtain ⟨hb', hhd', -⟩ := tile_lt hpre hco hj'
  obtain ⟨e1, e2, e3, e4, rfl⟩ := element_inj hhd (row_lt hpre hco hj st.isLt hy) (by omega) hz
    hhd' (row_lt hpre hco hj' st'.isLt hy') (by omega) hz' hloc
  -- the work items agree
  obtain ⟨htot, hG, hcs⟩ := hco
  have hW := hcs _ (htot ▸ hj)
  have hW' := hcs _ (htot ▸ hj')
  simp only [tileBatch, tileHead, tileRow, tileBlock, hW, hW'] at e1 e2 e3
  have hr := rankOf_eq hpre g
  have hr' := rankOf_eq hpre i'.1
  have hrl : ctaOf L g % 2 < 2 := Nat.mod_lt _ (by decide)
  have hrl' : ctaOf L i'.1 % 2 < 2 := Nat.mod_lt _ (by decide)
  rw [hr] at e3
  rw [hr'] at e3
  generalize hmw : workOf L g j % P.blocks = m at e3
  generalize hmw' : workOf L i'.1 j' % P.blocks = m' at e3
  have hst : st = st' := Fin.ext (by omega)
  have hyy : y = y' := by omega
  have hrk : ctaOf L g % 2 = ctaOf L i'.1 % 2 := by omega
  have hmm : m = m' := by omega
  have hhh : hh = hh' := Fin.ext (by omega)
  have hxx : x = x' := by omega
  subst hst hyy hhh hxx
  have hww : workOf L g j = workOf L i'.1 j' := work_eq e1 e2 (by rw [hmw, hmw', hmm])
  -- the cluster, the item and the CTA agree
  have hcl := clusterOf_lt hpre hgt
  have hcl' := clusterOf_lt hpre hgt'
  simp only [workOf, hG] at hww
  obtain ⟨rfl, hcc⟩ := Nat.digits_of_eq hcl hcl' (by rw [Nat.add_comm, hww, Nat.add_comm])
  rw [clusterOf_eq hpre, clusterOf_eq hpre] at hcc
  have hcta : ctaOf L g = ctaOf L i'.1 := by omega
  subst hpc'
  exact ⟨i'.1, i'.2, rfl, hgt', hcta.symm, hget', harr'⟩

/-- **The final memory of a complete execution is the specified output**, from the output's
writes and their values (`StoreValues`). -/
theorem post_of (hpre : Pre P L mem0) (hco : ItemCoords P L)
    (hX : Consistent L kernel asms mem0 X) (hd : Complete L X) (hs : StoreFacts P L X)
    (hw : WriteFacts L X) (hv : StoreValues P L X) {m : FinalMem} (hf : IsFinal L mem0 X m) :
    Post P mem0 m := by
  refine ⟨fun batch hb head hh row hr d hdd => memFloat_float fun k hk => ?_,
    fun l hsp hout => hf.unwritten (frame (writes_within_output hpre hco hX hs hw) hsp hout)⟩
  have hk2 : k < 2 := hk
  obtain ⟨g, kk, j, st, hh', x, y, hgt, hget, -, -, harr, hj, hx, hy, hbat, hhead, hrow,
    hdx⟩ := tile_store hpre hco hd hs hw hb hh hr hdd
  obtain ⟨hb', hhd', -⟩ := tile_lt hpre hco hj
  have hl := oSpec_writeLoc hx hy hk2 hh'.isLt (row_lt hpre hco hj st.isLt hy) hhd' hb'
  obtain ⟨o, b, ho, hwb, hmw⟩ := Complete.store_write hX hd ⟨_, hget⟩ hl
  have hcov : (⟨_, 1, false, false, .cta, 0, false⟩ : Acc).Covers ((elementLoc P P.oBase P.sq
      (tileBatch L g j) (tileHead L g j) (tileRow L g j st + y) (64 * hh' + x)).at k) :=
    ⟨rfl, rfl, Nat.le_refl _, Nat.lt_succ_self _⟩
  have hall := output_writers (st := st) (hh := hh') hpre hco hX hs hw hgt hj hx hy hk2
  -- each writer writes the tile's byte of the attention output
  have hval : ∀ {g' kk' : Nat} {o' : TensorStore.Observation} {b' : Byte},
      ctaOf L g' = ctaOf L g → X.get (g', kk') = some ⟨Store.Site.pc (.tma st hh'),
        .tensorStore P.oMap (oSpec P L g' j st hh')⟩ →
      arrivals (freeBar L (ctaOf L g') st) ((X.tr g').take kk') = j →
      X.tensorStores (g', kk') = some o' → TensorStore.writeByte o' x y k = some b' →
      b' = (Value.float .f16 (attn P (tileBatch L g j) (tileHead L g j) (tileRow L g j st + y)
        (64 * hh' + x))).byteAt k := by
    intro g' kk' o' b' hcta hget' harr' ho' hwb'
    have h := hv hget' harr' st.isLt hh'.isLt hx hy hk2 ho' hwb'
    simpa only [tileBatch, tileHead, tileRow, tileBlock, workOf, clusterOf, rankOf, hcta] using h
  have hfin := IsFinal.of_identical_writers hf (ws := storeWrites L X x y k)
    (fun w a bs hm hc => by
      obtain ⟨g', kk', rfl, hg', -, hget', -⟩ := hall w a bs hm hc
      exact mem_storeWrites hg' (len_of_get hget'))
    hmw hcov fun w a' bs' hm hc => by
      obtain ⟨g', kk', rfl, -, hcta, hget', harr'⟩ := hall w a' bs' hm hc
      have hsz : a'.size = 1 := by
        obtain ⟨-, -, -, -, -, -, -, hsz, -⟩ := hm
        exact hsz
      refine .inr ⟨hmw.intent, hm.intent, ⟨(Acc.loc_of_one hc hsz).symm, hsz.symm⟩,
        fun bs1 bs2 hw1 hw2 => ?_⟩
      obtain ⟨o1, -, b1, ho1, -, -, hb1, -, rfl, -⟩ := hw1
      obtain ⟨o2, -, b2, ho2, -, -, hb2, -, rfl, -⟩ := hw2
      rw [hval rfl hget harr ho1 hb1, hval hcta hget' harr' ho2 hb2]
  have hval0 := hval rfl hget harr ho hwb
  rw [← hbat, ← hhead, ← hrow, ← hdx, hfin]
  simp [wbyte, hval0]
  rfl

end Result

end

end PTX.Kernels.FlashAttn4Fwd.Proof
