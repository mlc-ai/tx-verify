-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.PrologueNonzeroTrace
public import Kernels.TmlFa4Fwd.Proof.PrologueRoles
public import Kernels.TmlFa4Fwd.Proof.TmemGeometry
public import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame
public import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixAlignment
public import Lemmas.Flow.Alloc
public import Lemmas.Flow.LoadShared
public import Lemmas.Flow.MemTmpl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

/-- The MMA warp keeps its shared base, both cuQ operands, used-K pointer and terminal O barrier. -/
def startupRegs : List Nat := [1062, 2535, 6495, 7502, 7506, 7503]

def startupFacts (p : Params) (l : Launch) : List (Nat × Value) :=
  [(1062, b32 12), (2535, b32 l.sharedBase), (6495, b32 (l.sharedBase + 144)),
    (7502, b64 p.cuQBase), (7506, b64 p.cuQBase), (7503, b64 p.usedKBase)]

private theorem startupFact_regs {p : Params} {l : Launch} :
    ∀ pair ∈ startupFacts p l, pair.1 ∈ startupRegs := by
  intro pair hm
  simp only [startupFacts, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [startupRegs]

private theorem mmaStartupCode :
    ((kernel.code.drop 1904).take 13).all (fun i => Assumptions.coreOp i.op) = true := by
  set_option maxRecDepth 100000 in
    kernel_rfl

/-- The decoded integer and event rules from the role branch through the first MMA broadcast. -/
theorem startupOut_eq_nil {l : Launch} {g : Nat} {t : TState}
    (hlo : 1904 ≤ t.pc) (hhi : t.pc < 1917) :
    out kernel Assumptions.all l g t = out kernel [] l g t := by
  cases hc : kernel.code[t.pc]? with
  | none => simp only [out, hc]
  | some ins =>
    have hi : ((kernel.code.drop 1904).take 13)[t.pc - 1904]? = some ins := by
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_sub_of_le hlo]
      exact hc
    have hCore := List.all_eq_true.mp mmaStartupCode ins (List.mem_of_getElem? hi)
    apply Assumptions.out_all_eq_nil _ _ _ hc hCore
    · simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    · simp only [Assumptions.tcLdDataflowSites, List.mem_cons, List.not_mem_nil, or_false]
      omega
    · simp only [Assumptions.delayedTmemSites, List.mem_cons, List.not_mem_nil, or_false]
      omega

variable {p : Params} {l : Launch}

private theorem dispatchCtaWord {m : Mem0} (hp : Pre p l m) {g : Nat} (hg : g < l.threads) :
    truncBits 32 (BitVec.ofNat 64 ((l.ctaidOf (g / l.block)).get .x)) =
      BitVec.ofNat 64 (g / l.block) := by
  have hCta : (l.ctaidOf (g / l.block)).get .x = g / l.block :=
    Option.some.inj (sregValue_oneDim hp.cluster.2.2 g).2.2.1
  have hBlock : 0 < l.block := by rw [hp.block]; decide
  have hGrid := (Nat.div_lt_iff_lt_mul hBlock).2 (show g < l.grid * l.block from hg)
  have hWord : g / l.block < 2 ^ 32 := lt_trans hGrid (lt_trans hp.grid.2.2 (by decide))
  rw [hCta, truncBits_ofNat hWord (by decide)]

private theorem dispatchFirst {m : Mem0} (hp : Pre p l m) {g : Nat} (hg : g < l.threads) :
    Seg kernel [] l g 4 174 [(1062, b32 12)] 1901 [(1072, b32 (g / l.block))] := by
  intro t ht
  have hCta := dispatchCtaWord hp hg
  seg_fp ht using simp only [b32, hCta]

private theorem dispatchBuffer {m : Mem0} (hp : Pre p l m) (g : Nat) :
    Seg kernel [] l g 3 1901 [(1062, b32 12), (2535, b32 l.sharedBase)] 1904
      [(1178, b32 (l.sharedBase + 68608))] := by
  intro t ht
  have hBase : l.sharedBase < 2 ^ 32 := by have := hp.shared.2.1; omega
  have hBuf : l.sharedBase + 68608 < 2 ^ 32 := by have := hp.shared.2.1; omega
  have hLit : truncBits 32 (BitVec.ofInt 64 68608) = BitVec.ofNat 64 68608 := rfl
  seg_fp ht using
    simp only [b32, hLit, truncBits_ofNat hBase (by decide), truncBits_ofNat hBuf (by decide),
      ← BitVec.ofNat_add]

private theorem dispatchRole (l : Launch) (g : Nat) :
    Seg kernel [] l g 2 1904 [(1062, b32 12)] 1906 [] := by
  intro t ht
  let u := next (setReg t 264 (.pred false))
  have hRun : run kernel [] l g 1 t = some u := by
    apply run_local Flow.code_1904 rfl ht
    rw [execLocalA_nil, execLocal_int rfl]
    simp only [execInt, DType.width, readBits, readReg, ht.2.2.2.2.1,
      bind, Except.bind, pure, Except.pure]
    rfl
  have hu : At u 1905 [(264, .pred false), (1062, b32 12)] := ht.set (by simp)
  obtain ⟨v, hv, hV⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g)
    Flow.code_1905 false hu hu.2.2.2.2.1 (by simp)
  exact ⟨v, run_comp hRun hv, hV.mono trivial⟩

set_option maxRecDepth 3000 in
theorem param19_name :
    param 19 = "kernel_cutlass_kernel_flash_attncuteflash_fwd_sm100FlashAttentionForwardSm100_\
      object_at__tensor000o111012_tensorptrbf16gmemalign16oi64div81i64div8i64div8_tensorptrbf16g\
      memalign16o1i64div8_0_param_19" := by
  have h : toString (19 : Nat) = "19" := by
    rw [Nat.toString_eq_repr, Nat.repr_eq_repr_append_repr (by decide)]
    simp only [show (19 / 10 : Nat) = 1 by decide, show (19 % 10 : Nat) = 9 by decide,
      Nat.repr_of_lt (n := 1) (by decide), Nat.repr_of_lt (n := 9) (by decide),
      Nat.digitChar_eq_one.mpr rfl, Nat.digitChar_eq_nine.mpr rfl]
    rfl
  unfold param
  rw [h]
  rfl

private theorem dispatchParam {m : Mem0} (hp : Pre p l m) {g : Nat} {t : TState}
    {F : List (Nat × Value)} (ht : At t 1906 F) (hF : ∀ pair ∈ F, pair.1 ≠ 7203) :
    ∃ u, run kernel Assumptions.all l g 1 t = some u ∧ At u 1907 ((7203, b32 p.batch) :: F) := by
  let u := next (setReg t 7203 (b32 p.batch))
  obtain ⟨hBound, hParam⟩ := hp.values (19, p.batch) (by simp [Params.scalarWords])
  change l.params (param 19) = some (BitVec.ofNat 64 p.batch) at hParam
  rw [param19_name] at hParam
  have hRun : run kernel [] l g 1 t = some u := by
    apply run_local Flow.code_1906 rfl ht
    rw [execLocalA_nil, execLocal_mem rfl]
    simp only [execMove, MemAccess.regs, List.filterMap_cons, List.filterMap_nil, id_eq, hParam,
      DType.width, MemExt.extendBits_same, pure, Except.pure, truncBits_ofNat hBound (by decide)]
    rfl
  have hActual := schedulerLocalTransport (A := Assumptions.all) (lo := 1906) (len := 1)
    rfl (fun hlo hhi => startupOut_eq_nil (by omega) (by omega)) hRun
    (by rw [ht.1]) (by rw [ht.1])
  exact ⟨u, hActual, ht.set hF⟩

private theorem dispatchLocal {l : Launch} {g pc n : Nat} {t u : TState} {R : List Nat}
    (hpc : t.pc = pc)
    (hOut : ∀ {s : TState}, pc ≤ s.pc → s.pc < pc + n →
      out kernel Assumptions.all l g s = out kernel [] l g s)
    (hWrites : ((kernel.code.drop pc).take n).all
      (fun ins => R.all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hStraight : ((kernel.code.drop pc).take (n - 1)).all
      (fun ins => schedulerFallsThrough ins.op) = true)
    (hr : run kernel [] l g n t = some u) :
    run kernel Assumptions.all l g n t = some u ∧ ∀ r ∈ R, u.regs r = t.regs r :=
  ⟨schedulerLocalTransport (lo := pc) (len := n) hStraight hOut hr
      hpc.ge (by rw [hpc]),
    fun _ h => schedulerLocalFrame hWrites hStraight hr hpc.ge (by rw [hpc]) h⟩

/-- The warp-12 dispatch preserves its launch words and reaches the 80-register hint. -/
theorem dispatchWarp12 {m : Mem0} (hp : Pre p l m) {g : Nat} (hg : g < l.threads) {t : TState}
    (ht : At t 174 (startupFacts p l)) :
    ∃ u, run kernel Assumptions.all l g 10 t = some u ∧
      At u 1907 ([(7203, b32 p.batch), (1178, b32 (l.sharedBase + 68608)),
        (1072, b32 (g / l.block))] ++ startupFacts p l) := by
  obtain ⟨a, ha, hA⟩ := dispatchFirst hp hg t (ht.mono ⟨ht.2.2.2.2.1, trivial⟩)
  obtain ⟨haAll, hFrameA⟩ := dispatchLocal (R := startupRegs) ht.1
    (fun hlo hhi => StartupAgreement.out_eq (.inl (by omega)))
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) ha
  have hKeepA := holdsSchedulerFrame ht.2.2.2.2 hFrameA startupFact_regs
  let F := (1072, b32 (g / l.block)) :: startupFacts p l
  have hAtA : At a 1901 F := hA.mono ⟨hA.2.2.2.2.1, hKeepA⟩
  obtain ⟨b, hb, hB⟩ := dispatchBuffer hp g a (hAtA.mono ⟨hKeepA.1, hKeepA.2.1, trivial⟩)
  obtain ⟨hbAll, hFrameB⟩ := dispatchLocal (R := 1072 :: startupRegs) hAtA.1
    (fun hlo hhi => StartupAgreement.out_eq (.inr (.inl (by omega))))
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hb
  have hF : ∀ pair ∈ F, pair.1 ∈ 1072 :: startupRegs := by
    intro pair hm
    rcases List.mem_cons.mp hm with rfl | hm
    · simp
    · exact List.mem_cons_of_mem _ (startupFact_regs pair hm)
  have hKeepB := holdsSchedulerFrame hAtA.2.2.2.2 hFrameB hF
  let G := (1178, b32 (l.sharedBase + 68608)) :: F
  have hAtB : At b 1904 G := hB.mono ⟨hB.2.2.2.2.1, hKeepB⟩
  obtain ⟨c, hc, hC⟩ := dispatchRole l g b (hAtB.mono ⟨hKeepB.2.1, trivial⟩)
  obtain ⟨hcAll, hFrameC⟩ := dispatchLocal (R := 1178 :: 1072 :: startupRegs) hAtB.1
    (fun hlo hhi => startupOut_eq_nil hlo (by omega))
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hc
  have hG : ∀ pair ∈ G, pair.1 ∈ 1178 :: 1072 :: startupRegs := by
    intro pair hm
    rcases List.mem_cons.mp hm with rfl | hm
    · simp
    · exact List.mem_cons_of_mem _ (hF pair hm)
  have hKeepC := holdsSchedulerFrame hAtB.2.2.2.2 hFrameC hG
  obtain ⟨u, hu, hU⟩ := dispatchParam hp (g := g) (hC.mono hKeepC) (by
    intro pair hm eq
    exact (of_decide_eq_true rfl : 7203 ∉ 1178 :: 1072 :: startupRegs) (eq ▸ hG pair hm))
  exact ⟨u, run_comp (run_comp (run_comp haAll hbAll) hcAll) hu, hU⟩

/-- The allocation's shared result address is the same for all lanes of this CTA. -/
def allocationSlot (l : Launch) (g : Nat) : Loc :=
  ⟨.shared, g / l.block, l.sharedBase + 312⟩

/-- The dispatch values and ABI operands needed after the register hint. -/
def entryFacts (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  [(7203, b32 p.batch), (1178, b32 (l.sharedBase + 68608)), (1072, b32 (g / l.block))] ++
    startupFacts p l

private theorem entryFacts_fresh {g r : Nat}
    (hr : r ∉ [7203, 1178, 1072, 1062, 2535, 6495, 7502, 7506, 7503]) :
    ∀ pair ∈ entryFacts p l g, pair.1 ≠ r := by
  intro pair hm hEq
  simp only [entryFacts, startupFacts, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hm hr
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

/-- The one-instruction allocation setup writes the literal number of columns. -/
theorem beforeAllocation {g : Nat} {t : TState} (ht : At t 1908 (entryFacts p l g)) :
    ∃ u, run kernel Assumptions.all l g 1 t = some u ∧
      At u 1909 ((2451, b32 512) :: entryFacts p l g) := by
  let u := next (setReg t 2451 (b32 512))
  have hRun : run kernel [] l g 1 t = some u := by
    apply run_local Flow.code_1908 rfl ht
    rfl
  have hActual := schedulerLocalTransport (A := Assumptions.all) (lo := 1908) (len := 1)
    rfl (fun hlo hhi => startupOut_eq_nil (by omega) (by omega)) hRun
    (by rw [ht.1]) (by rw [ht.1])
  exact ⟨u, hActual, ht.set (entryFacts_fresh (by decide))⟩

/-- The allocation and its address-store substep at the decoded TMEM instruction. -/
theorem allocationTemplate {m : Mem0} (hp : Pre p l m) {g : Nat} {t : TState} (hpc : t.pc = 1909)
    (hf : t.fault = none) (hBase : t.regs 2535 = some (b32 l.sharedBase))
    (hCols : t.regs 2451 = some (b32 512)) :
    out kernel Assumptions.all l g t = .ev
      (if t.sub = 0 then .tc (.resource .one (some (allocationSlot l g)) (.alloc 512))
        (if laneOf l g = 0 then { t with sub := 1 } else next t)
      else .tcAllocStore (allocationSlot l g) { t with pc := t.pc + 1, sub := 0 }) := by
  rw [startupOut_eq_nil (by rw [hpc]; decide) (by rw [hpc]; decide)]
  rw [out_event hf (by rw [hpc]; exact Flow.code_1909) rfl rfl]
  change Out.ev (tcTmpl l g t (.tcAlloc .one 2535 312 (.reg 2451))) = _
  have hBound : l.sharedBase + 312 < 2 ^ 32 := by have := hp.shared.2.1; omega
  have hAddr : effAddr l g t .shared 2535 312 = .ok (allocationSlot l g) :=
    effAddr_b32_off (off := 312) hBase hBound
  have hAlign : (allocationSlot l g).addr % 4 = 0 := by
    have h := hp.shared.1
    change (l.sharedBase + 312) % 4 = 0
    omega
  have hWarp : l.block % 32 = 0 := by rw [hp.block]
  have hColumns : readBits l g t 32 (.reg 2451) = .ok (BitVec.ofNat 64 512) := by
    simp only [readBits, readReg, hCols, b32, bind, Except.bind, pure, Except.pure]
    rfl
  have hValid : Tmem.validColumns (BitVec.ofNat 64 512).toNat = true := rfl
  by_cases hs : t.sub = 0 <;>
    simp only [tcTmpl, hWarp, hAddr, hColumns, hAlign, hValid, hs, ↓reduceIte,
      bind, Except.bind, pure, Except.pure, ofExec]
  rfl

/-- The address store is lane zero's second event at the allocation instruction. -/
theorem allocationStorePrefix {m : Mem0} {X : Execution} (hp : Pre p l m) {g pos : Nat} {t : TState}
    {o : Option TState} {facts : List (Nat × Value)} (hLane : laneOf l g = 0) (ht : At t 1909 facts)
    (hBase : t.regs 2535 = some (b32 l.sharedBase)) (hColumns : t.regs 2451 = some (b32 512))
    (hr : Run kernel Assumptions.all l g
      (if laneOf l g = 0 then { t with sub := 1 } else next t) ((X.tr g).drop pos) o)
    (hNonempty : (X.tr g).drop pos ≠ []) :
    ∃ col, col < 2 ^ 16 ∧
      X.get (g, pos) = some ⟨1909, .wr { loc := allocationSlot l g, size := 4 }
        ((b32 col).toBytes)⟩ ∧
      Run kernel Assumptions.all l g (next t) ((X.tr g).drop (pos+1)) o := by
  let s := { t with sub := 1 }
  have hpc : s.pc = 1909 := ht.1
  have hs : s.sub = 1 := rfl
  have hOut : out kernel Assumptions.all l g s =
      .ev (.tcAllocStore (allocationSlot l g) (next t)) := by
    rw [allocationTemplate hp hpc ht.2.2.2.1 hBase hColumns, hs]
    have hEq : { s with pc := s.pc + 1, sub := 0 } = next t := by
      have hs0 := ht.2.1
      cases t
      simp_all [s, next]
    simp only [Nat.one_ne_zero, ↓reduceIte, hEq]
  let hn : Next kernel Assumptions.all l g s s (.tcAllocStore (allocationSlot l g) (next t)) :=
    ⟨.refl, hOut⟩
  have hr' : Run kernel Assumptions.all l g s ((X.tr g).drop pos) o := by
    simpa only [hLane, ↓reduceIte, s] using hr
  obtain ⟨e, v, he, hf, hv⟩ := hn.continuing_at_nonempty (by
    rintro e ⟨col, hCol, he, hNone⟩
    cases hNone) hr' hNonempty
  obtain ⟨col, hCol, rfl, hEq⟩ := hf
  obtain rfl := Option.some.inj hEq
  exact ⟨col, hCol, by simpa only [hpc, b32] using he, hv⟩

/-- The exact trace index at the allocator's first 416-thread barrier. -/
def allocationBarrierPos (l : Launch) (g : Nat) : Nat :=
  if laneOf l g = 0 then 8 else 7

end
end PTX.Kernels.TmlFa4Fwd.Mma
