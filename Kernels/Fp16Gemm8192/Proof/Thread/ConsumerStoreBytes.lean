-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerOutEvents
public import Lemmas.Flow.StoreBytes

@[expose] public section

/-! # The bytes of a consumer's staging stores

Element `el` of chunk `i` of slice `k`'s stores writes the packed register holding the halves of the
accumulator values `32 k + 8 i + 2 el` (low half) and `32 k + 8 i + 2 el + 1` (high half)
(`store_bytes`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

namespace Consumer

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The packed registers a slice's chunk stores, by slice and chunk. -/
def storeSrcs (k i : Nat) : List Nat :=
  ([[[436, 437, 438, 439], [440, 441, 442, 443],
      [444, 445, 446, 447], [448, 449, 450, 451]],
    [[458, 459, 460, 461], [462, 463, 464, 465],
      [466, 467, 468, 469], [470, 471, 472, 473]],
    [[481, 482, 483, 484], [485, 486, 487, 488],
      [489, 490, 491, 492], [493, 494, 495, 496]],
    [[504, 505, 506, 507], [508, 509, 510, 511],
      [512, 513, 514, 515], [516, 517, 518, 519]],
    [[527, 528, 529, 530], [531, 532, 533, 534],
      [535, 536, 537, 538], [539, 540, 541, 542]],
    [[550, 551, 552, 553], [554, 555, 556, 557],
      [558, 559, 560, 561], [562, 563, 564, 565]],
    [[574, 575, 576, 577], [579, 580, 581, 582],
      [584, 585, 586, 587], [589, 590, 591, 592]],
    [[602, 603, 604, 605], [607, 608, 609, 610],
      [612, 613, 614, 615], [617, 618, 619, 620]]].getD k
    []).getD i []

/-- Each stored register packs the halves of two consecutive accumulator values (decided on the
tables). -/
theorem storeSrcs_pack : ∀ k < 8, ∀ i < 4, ∀ el < 4,
    (storeSrcs k i).length = 4 ∧
    dataTable.lookup ((storeSrcs k i).getD el 0) = none ∧
    packTable.lookup ((storeSrcs k i).getD el 0) =
      some (32 * k + 8 * i + 2 * el + 1, 32 * k + 8 * i + 2 * el) := by
  decide +kernel

/-- The instruction of a staging store: the slice's chunk's packed registers. -/
theorem code_store (k : Fin 8) (i el : Fin 4) {ins : Instr}
    (hc : kernel.code[(Site.store k i el).pc]? = some ins) :
    ins.op = .mem
      { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int .u 32,
        vec := ((storeSrcs k i).map Opnd.reg).length,
        addr := ⟨.reg (storeBase (k.val % 2) i) 32, 0⟩, srcs := (storeSrcs k i).map .reg } := by
  fin_cases k <;> fin_cases i <;> code_at hc <;> subst hc <;> rfl

/-- The stored registers are live at the store. -/
theorem storeSrcs_live (k : Fin 8) (i el : Fin 4) :
    ∀ r ∈ storeSrcs k i, r ∈ Flow.live (Site.store k i el).pc := by
  fin_cases k <;> fin_cases i <;> lit_mem

set_option maxHeartbeats 8000000 in
/-- **A staging store writes its packed halves.** -/
theorem store_bytes {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hat : (code L g).AtD (.inr (.cons d)) t) (htid : tidOf L g < 256) (hpre : Pre P L mem0)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) {k : Fin 8} {i el : Fin 4}
    (hs : d.site = .store k i el) :
    ∀ a bs, e.kind = .wr a bs → bs = (storeWord d.acc k i el).toBytes := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hst := setup_stageLt (tidOf L g) htid i i.isLt
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs hc hf hat ⊢
  subst hs
  have hsub : t.sub = el.val := hat.2.1
  have hreg : t.regs (storeBase (k.val % 2) i) =
      some (b32 (L.sharedBase + stagingOff (tidOf L g) (k.val % 2) i 0)) := by
    fin_cases k <;> fin_cases i <;> simp only [storeBase] <;>
      exact (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by cons_values; simp only [stagingOff]; congr 1; omega))
  have hlt : L.sharedBase + stagingOff (tidOf L g) (k.val % 2) i 0 < 2 ^ 32 := by
    simp only [stagingOff]; omega
  intro a bs hk
  rw [code_store k i el hc] at hf
  obtain ⟨hl, hd, hp⟩ := storeSrcs_pack k k.isLt i i.isLt el el.isLt
  have hmem : (storeSrcs k i).getD el 0 ∈ storeSrcs k i := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  have hsrc : ((storeSrcs k i).map Opnd.reg)[t.sub]? = some (.reg ((storeSrcs k i).getD el 0)) := by
    rw [hsub, List.getElem?_map, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl
  obtain ⟨v', hv', rfl⟩ := fires_stv32_bytes hreg hlt hsrc ((holds_mem hat.2.2.2.2
    (Flow.mem_factsFrom (storeSrcs_live k i el _ hmem))).trans
      (congrArg some (valueOf_pack hd hp)))
    (by rw [List.length_map, hl]; omega) hf a bs hk
  rw [storeValue_of_bytes (Flow.cvtPairV_bytes _ _)] at hv'
  cases hv'
  rfl

end Consumer

end

end PTX.Kernels.Fp16Gemm8192.Proof
