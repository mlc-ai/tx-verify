-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerOut
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerStart
public import Lemmas.Flow.Store
public import Lemmas.Flow.StoreValid
public import Kernels.Fp16Gemm8192.Data.TensorMaps

@[expose] public section

/-! # The events of a consumer's epilogue

Each slice's drain is a read wait retaining one bulk group (`drain_event`), the final drain a
full wait retaining none (`finalDrain_event`); element `el` of chunk `i` of slice `k`'s stores
writes four bytes of the staging buffer of the slice's parity (`store_event`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Consumer

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- A slice's drain waits for the reads of all but the latest bulk group. -/
theorem drain_event {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) {k : Fin 8} (hs : d.site = .drain k) :
    e = ⟨d.site.pc, .bulkWait .read 1⟩ := by
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs hc hf ⊢
  subst hs
  fin_cases k <;> code_at hc <;> subst hc <;> exact hf.1

/-- The final drain waits for every bulk group to complete. -/
theorem finalDrain_event {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hs : d.site = .finalDrain) :
    e = ⟨d.site.pc, .bulkWait .full 0⟩ := by
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs hc hf ⊢
  subst hs
  code_at hc
  subst hc
  exact hf.1

/-- The register holding the address of chunk `i` of a slice of parity `b`. -/
def storeBase (b i : Nat) : Nat :=
  (if b = 0 then [573, 578, 583, 588] else [601, 606, 611, 616]).getD
    i 0

/-- Element `el` of chunk `i` of slice `k`'s stores writes four staging bytes: the event is a write
or undefined behaviour, and a write is of four bytes at the element's footprint. -/
theorem store_event_all (hpre : Pre P L mem0) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hat : (code L g).AtD (.inr (.cons d)) t) (htid : tidOf L g < 256)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) {k : Fin 8} {i el : Fin 4}
    (hs : d.site = .store k i el) :
    ((∃ a bs, e.kind = .wr a bs) ∨ ∃ f, e.kind = .ub f) ∧
    ∀ a bs, e.kind = .wr a bs →
      (a.loc = ⟨.shared, g / L.block, L.sharedBase + stagingOff (tidOf L g) (k.val % 2) i el⟩ ∧
        a.size = 4) ∧ bs.length = 4 := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hst := setup_stageLt (tidOf L g) htid i i.isLt
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs hc hf hat ⊢
  subst hs
  have hsub : t.sub = el.val := hat.2.1
  obtain ⟨srcs, hlen4, hop⟩ : ∃ srcs, srcs.length = 4 ∧ ins.op = .mem
      { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int .u 32,
        vec := srcs.length, addr := ⟨.reg (storeBase (k.val % 2) i) 32, 0⟩,
        srcs := srcs } := by
    fin_cases k <;> fin_cases i <;> code_at hc <;> subst hc <;> exact ⟨[_, _, _, _], rfl, rfl⟩
  rw [hop] at hf
  have hreg : t.regs (storeBase (k.val % 2) i) =
      some (b32 (L.sharedBase + stagingOff (tidOf L g) (k.val % 2) i 0)) := by
    fin_cases k <;> fin_cases i <;> simp only [storeBase] <;>
      exact (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by cons_values; simp only [stagingOff]; congr 1; omega))
  have hlt : L.sharedBase + stagingOff (tidOf L g) (k.val % 2) i 0 < 2 ^ 32 := by
    simp only [stagingOff]; omega
  have hn : srcs.length = 1 ∨ srcs.length = 2 ∨ srcs.length = 4 := .inr (.inr hlen4)
  refine ⟨fires_stv32_kind hreg hlt hn hf, fun a bs hk => ?_⟩
  obtain ⟨h1, h2⟩ := fires_stv32 hreg hlt hn hf a bs hk
  refine ⟨⟨?_, h2⟩, fires_stv32_len hreg hlt hn hf a bs hk⟩
  rw [h1, hsub]
  simp only [stagingOff, Loc.mk.injEq, true_and]
  omega

theorem store_event (hpre : Pre P L mem0) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hat : (code L g).AtD (.inr (.cons d)) t) (htid : tidOf L g < 256)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) {k : Fin 8} {i el : Fin 4}
    (hs : d.site = .store k i el) :
    ∀ a bs, e.kind = .wr a bs →
      a.loc = ⟨.shared, g / L.block, L.sharedBase + stagingOff (tidOf L g) (k.val % 2) i el⟩ ∧
        a.size = 4 :=
  fun a bs hk => ((store_event_all hpre hat htid hc hf hs).2 a bs hk).1

/-- The register holding the staging buffer of slice parity `b`, the TMA store's source. -/
def tmaSrc (b : Nat) : Nat := if b = 0 then 596 else 624

/-- The register holding the output tensor map's address at slice `k`. -/
def tmaMap (k : Nat) : Nat :=
  [907, 909, 911, 913, 915, 917, 919, 921].getD k 0

/-- A slice's TMA store writes the output through the output tensor map from the staging buffer
of the slice's parity. -/
theorem tma_event (hpre : Pre P L mem0) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hat : (code L g).AtD (.inr (.cons d)) t) (htid : tidOf L g < 256)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) {k : Fin 8} (hs : d.site = .tma k) :
    ∀ a s, e.kind = .tensorStore a s → a = P.dMap ∧
      (⟨s.outer, s.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
        ⟨1, Fp16Gemm8192.mapD P.dBase P.dClass⟩ ∧
      s.sharedBase = ⟨.shared, g / L.block, L.sharedBase + stagingBase (tidOf L g) (k.val % 2)⟩ :=
        by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  intro a s hk
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs hc hf hat ⊢
  subst hs
  obtain ⟨cs, pol, hop⟩ : ∃ cs pol, ins.op = .cpTensorStore (.reg (tmaMap k)) cs
      (tmaSrc (k.val % 2)) 0 pol .tile none := by
    fin_cases k <;> code_at hc <;> subst hc <;> exact ⟨_, _, rfl⟩
  rw [hop] at hf
  obtain ⟨hsrc, hmap⟩ : t.regs (tmaSrc (k.val % 2)) =
        some (b32 (L.sharedBase + stagingBase (tidOf L g) (k.val % 2))) ∧
      t.regs (tmaMap k) = some (.ptr 64 true (.param "gemm_kernel_param_2") 0) := by
    fin_cases k <;> simp only [tmaSrc, tmaMap] <;>
      exact ⟨(holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by cons_values; simp only [stagingBase]; congr 1; omega)),
        (holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by cons_values))⟩
  obtain ⟨hma, ⟨dsc, hd, hdesc⟩, hsh⟩ := fires_cpTensorStore_spec hf a s hk
  have hlt : L.sharedBase + stagingBase (tidOf L g) (k.val % 2) < 2 ^ 32 := by
    simp only [stagingBase]; omega
  have hsh' : sharedEffAddr L g t false (tmaSrc (k.val % 2)) 0 =
      .ok ⟨.shared, g / L.block, L.sharedBase + stagingBase (tidOf L g) (k.val % 2)⟩ :=
    effAddr_b32 hsrc hlt
  rw [hsh'] at hsh
  have ha : a = P.dMap := by
    have h1 := hpre.mapAlignment.2.2
    have h2 := hpre.mapRange.2.2
    have hb : ({ name := "gemm_kernel_param_2", elementBits := 8, count := 128, alignment := 128 } :
        ParamObjectDecl).bytes = 128 := rfl
    simp [tensorMapAddress, readValue, readReg, hmap, hpre.paramD, mapParam, h1, bind,
      Except.bind, pure, Except.pure] at hma
    rw [hb, ite_eq_left ⟨le_refl _, by simpa using h2⟩] at hma
    exact (Except.ok.inj hma).symm
  subst ha
  rw [hpre.mapD] at hd
  refine ⟨rfl, ?_, (Except.ok.inj hsh).symm⟩
  simp only [TensorMode.transfer] at hdesc
  rw [hdesc]
  exact (Option.some.inj hd).symm


/-- A slice's TMA store specification is valid, with no row coordinates and no reduction. -/
theorem tma_valid {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) {k : Fin 8} (hs : d.site = .tma k) :
    ∀ a s, e.kind = .tensorStore a s →
      TensorStore.Valid (g / L.block) s ∧ s.rows = none ∧ s.reduce = none := by
  intro a s hk
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs hc hf
  subst hs
  obtain ⟨cs, pol, hop⟩ : ∃ cs pol, ins.op = .cpTensorStore (.reg (tmaMap k)) cs
      (tmaSrc (k.val % 2)) 0 pol .tile none := by
    fin_cases k <;> code_at hc <;> subst hc <;> exact ⟨_, _, rfl⟩
  rw [hop] at hf
  exact fires_cpTensorStore_form hf a s hk

/-- At a slice's TMA store the thread's latest event is its proxy fence. -/
def FenceRel (es : List Event) (d : D) : Prop :=
  ∀ k, d.site = .tma k →
    ∃ pc, es.getLast? = some ⟨pc, .fenceProxy (.async (some (.shared .cta))) none⟩

theorem fenceRel_step {d d' : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    {pre : List Event} (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hn : next L g d e = some (some d')) :
    FenceRel (pre ++ [e]) d' := by
  intro k hk
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  cases site
  case fence j =>
    simp only at hc hf
    have h : isFence e = true := by
      fin_cases j <;> code_at hc <;> subst hc <;> exact fence_fires hf
    unfold isFence at h
    have ek : e.kind = .fenceProxy (.async (some (.shared .cta))) none := by
      split at h
      · assumption
      · cases h
    obtain ⟨epc, ek'⟩ := e
    simp only at ek
    subst ek
    exact ⟨epc, by simp⟩
  all_goals exfalso
  all_goals clear hc hf
  all_goals simp only [next] at hn
  clc_sweep hn
  all_goals simp_all

/-- Every byte a store through the output map reads lies in the 8 KB box at its shared base. -/
theorem mapD_readLoc {b : Nat} {cls : TensorDescriptor.AllocationClass} {s : TensorStore.Spec}
    (hd : (⟨s.outer, s.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
      ⟨1, Fp16Gemm8192.mapD b cls⟩) {x y k : Nat} {l : Loc}
    (h : TensorStore.readLoc s x y k = some l) :
    l.space = s.sharedBase.space ∧ l.cta = s.sharedBase.cta ∧ s.sharedBase.addr ≤ l.addr ∧
      l.addr < s.sharedBase.addr + 8192 := by
  obtain ⟨⟨outer, desc, origin, sb, rows⟩, red⟩ := s
  simp only [Sigma.mk.injEq] at hd
  obtain ⟨rfl, hdesc⟩ := hd
  cases hdesc
  simp only [TensorStore.readLoc, TensorTransfer.slotAt, Option.map_eq_some_iff] at h
  obtain ⟨slot, hslot, rfl⟩ := h
  split_ifs at hslot with hx hy hb
  cases hslot
  simp only [Fp16Gemm8192.mapD, encodeTiled, TensorTile.count, TensorTile.step, TensorTile.rows,
    TensorTile.rowsOf, TensorDescriptor.Format.bytes] at hx hy hb
  have hbd := swizzle_offset_bounds .b64 sb.addr
    (TensorTile.linearByte (Fp16Gemm8192.mapD b cls).box 2 .b64 x y k)
  simp only [TensorBox.sharedLoc, TensorTile.sharedByte]
  simp only [Fp16Gemm8192.mapD, encodeTiled, TensorTile.linearByte, TensorTile.rowBytes,
    TensorTile.swizzleWidth, TensorDescriptor.Format.bytes] at hbd ⊢
  simp [TensorTile.count, TensorTile.step,
    Fin.succ_zero_eq_one] at hx hy hbd ⊢
  omega

/-- The drains of a consumer's trace. At a slice's first barrier its latest event is its drain; at
its final drain its latest event is the last slice's bulk commit; and past its final drain (from
its exit barrier on), the final drain's wait for every bulk group (`bulkWait .full 0`), right after
that commit, is an event of the trace and no tensor store follows it. -/
def DrainRel (es : List Event) (d : D) : Prop :=
  (∀ k, d.site = .barA k → ∃ pc, es.getLast? = some ⟨pc, .bulkWait .read 1⟩) ∧
  (d.site = .finalDrain → ∃ pc, es.getLast? = some ⟨pc, .bulkCommit⟩) ∧
  (d.drained = true → ∃ j pc pc', 0 < j ∧ es[j]? = some ⟨pc, .bulkWait .full 0⟩ ∧
    es[j - 1]? = some ⟨pc', .bulkCommit⟩ ∧ ∀ i, j ≤ i → ∀ e a s, es[i]? = some e →
      e.kind ≠ .tensorStore a s)


/-- The slice and the number of staging stores a state has made in it: the position of a store site
(the stores before it), and sixteen at the slice's second barrier. -/
def D.storePos (d : D) : Option (Fin 8 × Nat) :=
  match d.site with
  | .store k i el => some (k, 4 * i.val + el.val)
  | .barB k => some (k, 16)
  | _ => none

/-- On a trace without undefined behaviour, the staging stores of the slice a thread is in are its
latest events: element `m` of the slice (chunk `m / 4`, element `m % 4`) is the write of that
element's four bytes. -/
def StoreRel (L : Launch) (g : Nat) (d : D) (es : List Event) : Prop :=
  (∀ e ∈ es, ∀ f, e.kind ≠ .ub f) → ∀ k n, d.storePos = some (k, n) → n ≤ es.length ∧
    ∀ m, m < n → ∃ pc a bs, es[es.length - n + m]? = some ⟨pc, .wr a bs⟩ ∧
      a.loc = ⟨.shared, g / L.block,
        L.sharedBase + stagingOff (tidOf L g) (k.val % 2) (m / 4) (m % 4)⟩ ∧
      a.size = 4 ∧ bs.length = 4

theorem storeRel_step (hpre : Pre P L mem0) {d d' : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {pre : List Event} (hat : (code L g).AtD (.inr (.cons d)) t)
    (htid : tidOf L g < 256) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hn : next L g d e = some (some d'))
    (hq : StoreRel L g d pre) : StoreRel L g d' (pre ++ [e]) := by
  intro hnu k n hpos
  have hnu' : ∀ x ∈ pre, ∀ f, x.kind ≠ .ub f :=
    fun x hx f => hnu x (List.mem_append_left _ hx) f
  have hne : ∀ f, e.kind ≠ .ub f :=
    fun f => hnu e (List.mem_append_right _ (List.mem_singleton.mpr rfl)) f
  obtain ⟨site, mm, n0, m', n', cp, ap, resp, x, acc, base⟩ := d
  cases site
  case store k0 i el =>
    obtain ⟨hk, hall⟩ := store_event_all hpre hat htid hc hf (k := k0) (i := i) (el := el) rfl
    obtain ⟨a, bs, hkind⟩ : ∃ a bs, e.kind = .wr a bs :=
      hk.resolve_right (by rintro ⟨f, hf'⟩; exact hne f hf')
    obtain ⟨⟨hloc, hsize⟩, hlen⟩ := hall a bs hkind
    obtain ⟨hle, hst⟩ := hq hnu' k0 (4 * i.val + el.val) rfl
    have hi := i.isLt
    have hel := el.isLt
    have hpos' : n = 4 * i.val + el.val + 1 ∧ k = k0 := by
      simp only [next] at hn
      split_ifs at hn <;> simp only [Option.some.injEq] at hn <;> subst hn <;>
        simp only [D.storePos, Option.some.injEq, Prod.mk.injEq] at hpos <;> omega
    obtain ⟨hn1, hk1⟩ := hpos'
    subst hn1 hk1
    obtain ⟨epc, ek⟩ := e
    simp only at hkind
    subst hkind
    refine ⟨by simp only [List.length_append, List.length_singleton]; omega, fun m hm => ?_⟩
    have hidx : (pre ++ [(⟨epc, .wr a bs⟩ : Event)]).length - (4 * i.val + el.val + 1) + m =
        pre.length - (4 * i.val + el.val) + m := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [hidx]
    by_cases hm' : m < 4 * i.val + el.val
    · obtain ⟨pc, a', bs', h1, h2, h3, h4⟩ := hst m hm'
      refine ⟨pc, a', bs', ?_, h2, h3, h4⟩
      rw [List.getElem?_append_left (by omega)]
      exact h1
    · have hmeq : m = 4 * i.val + el.val := by omega
      refine ⟨epc, a, bs, ?_, ?_, hsize, hlen⟩
      · rw [show pre.length - (4 * i.val + el.val) + m = pre.length by omega]
        simp
      · rw [hloc, hmeq]
        simp only [Loc.mk.injEq, true_and]
        congr 2 <;> omega
  case barA k0 =>
    simp only [next, Option.some.injEq] at hn
    subst hn
    simp only [D.storePos, Option.some.injEq, Prod.mk.injEq] at hpos
    obtain ⟨-, rfl⟩ := hpos
    exact ⟨Nat.zero_le _, fun m hm => absurd hm (Nat.not_lt_zero _)⟩
  all_goals exfalso
  all_goals clear hq hc hf hat hnu hnu' hne
  all_goals simp only [next] at hn
  clc_sweep hn
  all_goals simp_all [D.storePos]

/-- The latest events of a thread at its proxy fence and at its TMA store: the output barrier
arrival (the fence follows it directly), then the fence. -/
def BarRel (L : Launch) (g : Nat) (d : D) (es : List Event) : Prop :=
  (∀ k, d.site = .fence k →
      ∃ pc, es.getLast? = some ⟨pc, .bar (outId L g) (some 128)⟩) ∧
    ∀ k, d.site = .tma k →
      2 ≤ es.length ∧ ∃ pc, es[es.length - 2]? = some ⟨pc, .bar (outId L g) (some 128)⟩

theorem barRel_step (hpre : Pre P L mem0) {d d' : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {pre : List Event} (hat : (code L g).AtD (.inr (.cons d)) t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hn : next L g d e = some (some d'))
    (hq : BarRel L g d pre) : BarRel L g d' (pre ++ [e]) := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · obtain ⟨site, mm, n0, m', n', cp, ap, resp, x, acc, base⟩ := d
    cases site
    case barB k0 =>
      have he := out_bar_event hpre hat hc hf (k := k0) (.inr rfl)
      subst he
      exact ⟨_, List.getLast?_concat⟩
    all_goals exfalso
    all_goals clear hq hc hf hat
    all_goals simp only [next] at hn
    clc_sweep hn
    all_goals simp_all
  · obtain ⟨site, mm, n0, m', n', cp, ap, resp, x, acc, base⟩ := d
    cases site
    case fence k0 =>
      obtain ⟨pc, hl⟩ := hq.1 k0 rfl
      have hlen : 0 < pre.length := List.length_pos_of_ne_nil (by rintro rfl; simp at hl)
      refine ⟨by simp only [List.length_append, List.length_singleton]; omega, pc, ?_⟩
      rw [show (pre ++ [e]).length - 2 = pre.length - 1 by simp,
        List.getElem?_append_left (by omega), ← List.getLast?_eq_getElem?]
      exact hl
    all_goals exfalso
    all_goals clear hq hc hf hat
    all_goals simp only [next] at hn
    clc_sweep hn
    all_goals simp_all

end Consumer

end
end PTX.Kernels.Fp16Gemm8192.Proof
