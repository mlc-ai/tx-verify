-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsStoreCoords
public import Kernels.FlashAttn4Fwd.Proof.Thread.StoreCounts
public import Lemmas.Flow.TensorStoreOrigin
public import Lemmas.Flow.TensorStoreOk

@[expose] public section

/-! # The specification of a TMA store

A TMA store of the store warp at site `tma st hh` of item `i < T` fires the store of half `hh` of
stage `st` of the item and no undefined behaviour (`Store.tma_event`, mirroring the loader's
`copy_is`): the O map at the map parameter `param_7` (`O_map_ok`), the coordinates the item's
registers hold (head dimension `64 hh`, row `512 m + 256 st + 128 r` (`Store.orow_val`), head,
batch), from the stage half's 128-aligned buffer of the thread's CTA. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t : TState}

theorem oOrigin_0 {L : Launch} {g j st hh : Nat} (h : 0 < 4) :
    oOrigin L g j st hh ⟨0, h⟩ = ((64 * hh : Nat) : Int) := rfl
theorem oOrigin_1 {L : Launch} {g j st hh : Nat} (h : 1 < 4) :
    oOrigin L g j st hh ⟨1, h⟩ = ((tileRow L g j st : Nat) : Int) := rfl
theorem oOrigin_2 {L : Launch} {g j st hh : Nat} (h : 2 < 4) :
    oOrigin L g j st hh ⟨2, h⟩ = ((tileHead L g j : Nat) : Int) := rfl
theorem oOrigin_3 {L : Launch} {g j st hh : Nat} (h : 3 < 4) :
    oOrigin L g j st hh ⟨3, h⟩ = ((tileBatch L g j : Nat) : Int) := rfl

/-- The O map, read through its parameter, is the launch's valid map. -/
theorem O_map_ok (hpre : Pre P L mem0) {cs : List Opnd} (hcs : cs.length = 4)
    (hr : t.regs 4099 = some (.ptr 64 true (.param (param "7")) 0)) :
    tensorMap L g t (.reg 4099) cs .tile =
      .ok (P.oMap, ⟨3, FlashAttn4Fwd.mapO P.oBase P.sq P.h P.b P.oFill P.oClass⟩) := by
  have hal := hpre.mapAlignment
  have hra := hpre.mapRange
  have hta := hpre.tensorAlignment
  have hsq := hpre.sqRange
  have hsqp := hpre.sqPos
  have hst := hpre.strideRange
  have hbr := hpre.batchRange
  have hbp := hpre.bPos
  have hhp := hpre.hPos
  have hv : TensorDescriptor.Valid (FlashAttn4Fwd.mapO P.oBase P.sq P.h P.b P.oFill P.oClass) :=
    encodeTiled_valid hta.2.2.2 ⟨hsqp, by omega⟩ hhp ⟨hbp, hbr⟩ hst.1 ⟨by decide, by decide⟩
  simp [tensorMap, tensorMapAddress, readValue, readReg, hr, hpre.paramO, mapParam,
    ParamObjectDecl.bytes, hpre.mapO, hv, hcs, TensorMode.coordinates, hal.2.2.2,
    show P.oMap ≤ 18446744073709551488 by omega, bind, Except.bind, pure, Except.pure]

/-- **A TMA store whose operand registers hold the item's coordinates** fires the store of its
half of its stage of its item, and no undefined behaviour. -/
theorem Store.tma_of_regs (hpre : Pre P L mem0) {pc r0 r1 src : Nat} {e : Event}
    {o : Option TState} (st hh : Fin 2) (i : Nat) (hi : i < Work.T L g)
    (hf : Fires pc (eventTmpl asms L g t (.cpTensorStore (.reg 4099)
      [.reg r0, .reg r1, .reg 3927, .reg 3926] src 0 (some (.reg 4100)) .tile none)) e o)
    (hmap : t.regs 4099 = some (.ptr 64 true (.param (param "7")) 0))
    (hpol : t.regs 4100 = some (.bits 64 (truncBits 64 (BitVec.ofInt 64 0))))
    (h0 : t.regs r0 = some (b32 (64 * hh.val))) (h1 : t.regs r1 = some (b32 (tileRow L g i st)))
    (h2 : t.regs 3927 = some (b32 (tileHead L g i)))
    (h3 : t.regs 3926 = some (b32 (tileBatch L g i)))
    (hsrc : t.regs src = some (b32 (stageBase L st hh))) :
    e.kind = .tensorStore P.oMap (oSpec P L g i st hh) := by
  obtain ⟨-, hb, hh', hm⟩ := Work.Dm.item_bounds hpre hi
  have hsq := hpre.sqRange
  have hbase := hpre.sharedRange
  have hal := hpre.sharedAlignment
  unfold sharedBytes at hbase
  have hst : st.val < 2 := st.isLt
  have hhv : hh.val < 2 := hh.isLt
  have hrb : tileRow L g i st < 2 ^ 31 := by
    have := rankOf_eq hpre g
    have : Work.rank L g < 2 := Nat.mod_lt _ (by decide)
    simp only [tileRow, tileBlock]
    omega
  have hs := sharedEffAddr_b32 (L := L) (g := g) hsrc (by simp only [stageBase]; omega)
  rcases fires_cpTensorStore_kind hf with ⟨a, s, hk⟩ | ⟨f, hk⟩
  · have hok := fires_cpTensorStore_ok hf hk
    obtain ⟨hma, dd, hdd, -, hdesc, hrows, hred⟩ := tensorStoreSpec_ok hok
    obtain ⟨-, -, hsb⟩ := fires_cpTensorStore_spec hf a s hk
    obtain ⟨decl, hdecl⟩ := tensorMapAddress_param hmap hma
    rw [hpre.paramO] at hdecl
    have ha : a = P.oMap := (Prod.mk.inj (Option.some.inj hdecl)).2.symm
    subst ha
    rw [hpre.mapO] at hdd
    have hsig := Option.some.inj hdd
    have hor := tensorStoreSpec_origin_regs hok h0 h1 h2 h3 (by omega) hrb hh' hb
    rw [hs] at hsb
    rw [hk]
    congr 1
    obtain ⟨⟨outer, desc, origin, sb, rows⟩, red⟩ := s
    simp only at hsig hdesc hrows hred hsb hor
    obtain ⟨rfl, hdd'⟩ := Sigma.mk.inj hsig
    have hdd'' := eq_of_heq hdd'
    simp only [TensorMode.transfer] at hdesc
    subst hdesc hdd'' hred
    have hrw : rows = none := by simpa using hrows
    subst hrw
    simp only [oSpec, TensorStore.Spec.mk.injEq, TensorBox.mk.injEq, heq_eq_eq, true_and,
      and_true]
    refine ⟨?_, ?_⟩
    · funext x
      rw [hor x]
      rcases x with ⟨_ | _ | _ | _ | n, hn⟩
      · rw [oOrigin_0]; rfl
      · rw [oOrigin_1]; rfl
      · rw [oOrigin_2]; simp only [List.getD_cons_succ, List.getD_cons_zero]
      · rw [oOrigin_3]; simp only [List.getD_cons_succ, List.getD_cons_zero]
      · omega
    · rw [← Except.ok.inj hsb]
      simp only [ctaOf]
  · refine absurd (fires_ub hf hk) (cpTensorStore_ok ?_ (O_map_ok hpre rfl hmap) hs
      (by simp only [stageBase]; omega) (vs := [BitVec.ofNat 64 (64 * hh.val),
        BitVec.ofNat 64 (tileRow L g i st), BitVec.ofNat 64 (tileHead L g i),
        BitVec.ofNat 64 (tileBatch L g i)]) ?_ ?_ ?_ f)
    · simp [cachePolicyRead, readBits, readReg, hpol, truncBits, bind, Except.bind, pure,
        Except.pure]
    · simp only [List.mapM_cons, List.mapM_nil, readBits_b32 h0 (by omega),
        readBits_b32 h1 (by omega), readBits_b32 h2 (by simp only [tileHead]; omega),
        readBits_b32 h3 (by simp only [tileBatch]; omega), bind, Except.bind, pure, Except.pure]
    · have e : ∀ x : Nat, x < 2 ^ 31 → 0 ≤ (BitVec.ofNat 32 (BitVec.ofNat 64 x).toNat).toInt :=
        fun x hx => by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), toInt_ofNat_lt32 hx]
          omega
      intro n
      rcases n with _ | _ | _ | _ | n
      · exact e _ (by omega)
      · exact e _ hrb
      · exact e _ hh'
      · exact e _ hb
      · simp [List.getD]
    · simp only [TensorDescriptor.BoxAligned, mapO, encodeTiled, TensorDescriptor.Format.bytes,
        Fin.val_zero, List.getD_cons_zero, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), toInt_ofNat_lt32 (by omega)]
      omega

/-- **The event of a TMA site** of item `i < T` is the store of its half of its stage of the
item. -/
theorem Store.tma_event (hpre : Pre P L mem0) {st hh : Fin 2} {i : Nat} {ins : Instr}
    {e : Event} {o : Option TState} (hi : i < Work.T L g)
    (h : Holds t.regs (Store.facts L g ⟨.tma st hh, i⟩))
    (hc : kernel.code[(Store.Site.tma st hh).pc]? = some ins)
    (hf : Fires (Store.Site.tma st hh).pc (eventTmpl asms L g t ins.op) e o) :
    e.kind = .tensorStore P.oMap (oSpec P L g i st hh) := by
  obtain ⟨hw, hb, hh', hm⟩ := Work.Dm.item_bounds hpre hi
  have hsq := hpre.sqRange
  have hmm : 512 * (coordsOf L (workOf L g i)).2.2 + 512 < 2 ^ 31 := by omega
  have hw32 : workOf L g i < 2 ^ 32 := by omega
  have hrk := rankOf_eq hpre g
  have reg : ∀ r, r ∈ Flow.live (Store.Site.tma st hh).pc → ∀ {v},
      Store.valueOf L g ⟨.tma st hh, i⟩ r = v → t.regs r = some v := fun r hl v hv => by
    rw [← hv]; exact holds_mem h (mem_factsFrom hl)
  have e0 : 512 * (coordsOf L (workOf L g i)).2.2 + 128 * Work.rank L g = tileRow L g i 0 := by
    simp only [tileRow, tileBlock, hrk, Work.rank]
    omega
  have e1 : 512 * (coordsOf L (workOf L g i)).2.2 + 128 * Work.rank L g + 256 =
      tileRow L g i 1 := by
    simp only [tileRow, tileBlock, hrk, Work.rank]
    omega
  have v1 : Store.valueOf L g ⟨.tma st hh, i⟩ 4099 = .ptr 64 true (.param (param "7")) 0 := rfl
  have v2 : Store.valueOf L g ⟨.tma st hh, i⟩ 4100 =
      .bits 64 (truncBits 64 (BitVec.ofInt 64 0)) := rfl
  have v3 : Store.valueOf L g ⟨.tma st hh, i⟩ 3927 = b32 (tileHead L g i) := by
    simp only [Store.valueOf, Store.table, PTX.Flow.lookupLit, Option.getD_some,
      Work.Dm.headW_eq hpre hw32, tileHead, b32]
  have v4 : Store.valueOf L g ⟨.tma st hh, i⟩ 3926 = b32 (tileBatch L g i) := by
    simp only [Store.valueOf, Store.table, PTX.Flow.lookupLit, Option.getD_some,
      Work.Dm.batchW_eq hpre hw32, tileBatch, b32]
  have v5 : Store.valueOf L g ⟨.tma st hh, i⟩ 974 = b32 (64 * (0 : Fin 2).val) := rfl
  have v6 : Store.valueOf L g ⟨.tma st hh, i⟩ 975 = b32 (64 * (1 : Fin 2).val) := rfl
  have v7 : Store.valueOf L g ⟨.tma st hh, i⟩ 973 = b32 (tileRow L g i (0 : Fin 2)) := by
    simp only [Store.valueOf, Store.table, PTX.Flow.lookupLit, Option.getD_some,
      Store.orow_val hpre hw32 hmm, e0, b32, Fin.val_zero]
  have v8 : Store.valueOf L g ⟨.tma st hh, i⟩ 976 = b32 (tileRow L g i (1 : Fin 2)) := by
    simp only [Store.valueOf, Store.table, PTX.Flow.lookupLit, Option.getD_some,
      Store.orow256_val hpre hw32 hmm, e1, b32, Fin.val_one]
  have v9 : Store.valueOf L g ⟨.tma st hh, i⟩ 399 = b32 (stageBase L (0 : Fin 2) (0 : Fin 2)) := rfl
  have v10 : Store.valueOf L g ⟨.tma st hh, i⟩ 396 =
      b32 (stageBase L (0 : Fin 2) (1 : Fin 2)) := rfl
  have v11 : Store.valueOf L g ⟨.tma st hh, i⟩ 397 =
      b32 (stageBase L (1 : Fin 2) (0 : Fin 2)) := rfl
  have v12 : Store.valueOf L g ⟨.tma st hh, i⟩ 398 =
      b32 (stageBase L (1 : Fin 2) (1 : Fin 2)) := rfl
  rcases Store.fin2_cases st with rfl | rfl <;> rcases Store.fin2_cases hh with rfl | rfl
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_10)
    exact Store.tma_of_regs hpre 0 0 i hi hf (reg _ (by table_decide) v1)
      (reg _ (by table_decide) v2) (reg _ (by table_decide) v5) (reg _ (by table_decide) v7)
      (reg _ (by table_decide) v3) (reg _ (by table_decide) v4) (reg _ (by table_decide) v9)
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_11)
    exact Store.tma_of_regs hpre 0 1 i hi hf (reg _ (by table_decide) v1)
      (reg _ (by table_decide) v2) (reg _ (by table_decide) v6) (reg _ (by table_decide) v7)
      (reg _ (by table_decide) v3) (reg _ (by table_decide) v4) (reg _ (by table_decide) v10)
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_12)
    exact Store.tma_of_regs hpre 1 0 i hi hf (reg _ (by table_decide) v1)
      (reg _ (by table_decide) v2) (reg _ (by table_decide) v5) (reg _ (by table_decide) v8)
      (reg _ (by table_decide) v3) (reg _ (by table_decide) v4) (reg _ (by table_decide) v11)
  · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tensorCopy_13)
    exact Store.tma_of_regs hpre 1 1 i hi hf (reg _ (by table_decide) v1)
      (reg _ (by table_decide) v2) (reg _ (by table_decide) v6) (reg _ (by table_decide) v8)
      (reg _ (by table_decide) v3) (reg _ (by table_decide) v4) (reg _ (by table_decide) v12)

end
end PTX.Kernels.FlashAttn4Fwd.Proof
