-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EvDProSites

@[expose] public section

/-!
# Event shapes of the prologue: elections, barrier initializations, arrivals, barriers, role table

What the prologue's synchronization events are, over its abstract states:

* `sMax`: the request to raise the register budget to 256;
* `elSite i`: a full-mask `elect.sync` (member mask `0xFFFFFFFF`); the leader is free;
* `inSite i`: `mbarrier.init` with arrival count 1 of the barrier `initBar i` of the thread's own
  CTA (`EvD.Bar.loc`), which is the order `kv_ready 0`, `kv_empty 0`, `kv_ready 1`, `kv_empty 1`,
  `kv_ready 2`, `kv_empty 2`, `s_ready 0`, `p_ready 0`, `s_ready 1`, `p_ready 1`, `o_done`,
  `o_final` (`val_init`: the address registers hold `sharedBase + Bar.off`);
* `arrSite j`: the `expect_tx` arrival of 65536 bytes, one arrival, release at CTA scope, on
  `kv_ready j`;
* `fnc0`, `fnc1`: the proxy fence of the async proxy on shared memory;
* `bar2` and the preload's barriers: `bar.sync 0, 128`; `bar18`: `bar.sync 1`;
* `psh j`: the full-warp `shfl.sync.idx` of the warp index from lane 0;
* `st8`: the four bytes of the role table `0x01000202` at `sharedBase + 213336`;
* `st9_0`, `st9_1`: the two words of `(num_pre, num_iters)` at `sharedBase + 212992` and `+ 4`
  (the values are `numPreW`, `numItersW`; `st9_values` ties them to `Spec`: `numPre` and
  `numIters` of the thread's request and split).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d : D} {e : Event} {u : TState}

/-- The barrier the `i`-th mbarrier initialization of the prologue initializes. -/
def initBars : List Bar :=
  [.kvReady 0, .kvEmpty 0, .kvReady 1, .kvEmpty 1, .kvReady 2, .kvEmpty 2, .sReady 0, .pReady 0,
    .sReady 1, .pReady 1, .oDone, .oFinal]

def initBar (i : Nat) : Bar := initBars.getD i .oFinal

/-- The address registers of the initializations hold `sharedBase + off` of their barrier. -/
theorem val_init (L : Launch) (g : Nat) (dt : Dat) :
    ∀ i < 12, valueOf L g dt (613 + i) =
      b32 ((L.sharedBase + (initBar i).off) % 2 ^ 32) := by
  intro i hi
  interval_cases i
  · show Value.bits 32 (v_r152 L g dt) = _
    have hw := wAdd32_smem L 213216 (by decide)
    have ht : (213216 : Int).toNat = 213216 := by decide
    rw [ht] at hw
    have : v_r152 L g dt = BitVec.ofNat 64 ((L.sharedBase + 213216) % 2 ^ 32) := by
      simp only [v_r152, v_r205, hw]
    rw [this]; rfl
  · show Value.bits 32 (v_r153 L g dt) = _
    have hw := wAdd32_smem L 213248 (by decide)
    have ht : (213248 : Int).toNat = 213248 := by decide
    rw [ht] at hw
    have : v_r153 L g dt = BitVec.ofNat 64 ((L.sharedBase + 213248) % 2 ^ 32) := by
      simp only [v_r153, v_r205, hw]
    rw [this]; rfl
  · show Value.bits 32 (v_r154 L g dt) = _
    have hw := wAdd32_smem L 213224 (by decide)
    have ht : (213224 : Int).toNat = 213224 := by decide
    rw [ht] at hw
    have : v_r154 L g dt = BitVec.ofNat 64 ((L.sharedBase + 213224) % 2 ^ 32) := by
      simp only [v_r154, v_r205, hw]
    rw [this]; rfl
  · show Value.bits 32 (v_r155 L g dt) = _
    have hw := wAdd32_smem L 213256 (by decide)
    have ht : (213256 : Int).toNat = 213256 := by decide
    rw [ht] at hw
    have : v_r155 L g dt = BitVec.ofNat 64 ((L.sharedBase + 213256) % 2 ^ 32) := by
      simp only [v_r155, v_r205, hw]
    rw [this]; rfl
  · show Value.bits 32 (v_r156 L g dt) = _
    have hw := wAdd32_smem L 213232 (by decide)
    have ht : (213232 : Int).toNat = 213232 := by decide
    rw [ht] at hw
    have : v_r156 L g dt = BitVec.ofNat 64 ((L.sharedBase + 213232) % 2 ^ 32) := by
      simp only [v_r156, v_r205, hw]
    rw [this]; rfl
  · show Value.bits 32 (v_r157 L g dt) = _
    have hw := wAdd32_smem L 213264 (by decide)
    have ht : (213264 : Int).toNat = 213264 := by decide
    rw [ht] at hw
    have : v_r157 L g dt = BitVec.ofNat 64 ((L.sharedBase + 213264) % 2 ^ 32) := by
      simp only [v_r157, v_r205, hw]
    rw [this]; rfl
  · show Value.bits 32 (v_r158 L g dt) = _
    have hw := wAdd32_smem L 213280 (by decide)
    have ht : (213280 : Int).toNat = 213280 := by decide
    rw [ht] at hw
    have : v_r158 L g dt = BitVec.ofNat 64 ((L.sharedBase + 213280) % 2 ^ 32) := by
      simp only [v_r158, v_r205, hw]
    rw [this]; rfl
  · show Value.bits 32 (v_r159 L g dt) = _
    have hw := wAdd32_smem L 213296 (by decide)
    have ht : (213296 : Int).toNat = 213296 := by decide
    rw [ht] at hw
    have : v_r159 L g dt = BitVec.ofNat 64 ((L.sharedBase + 213296) % 2 ^ 32) := by
      simp only [v_r159, v_r205, hw]
    rw [this]; rfl
  · show Value.bits 32 (v_r160 L g dt) = _
    have hw := wAdd32_smem L 213288 (by decide)
    have ht : (213288 : Int).toNat = 213288 := by decide
    rw [ht] at hw
    have : v_r160 L g dt = BitVec.ofNat 64 ((L.sharedBase + 213288) % 2 ^ 32) := by
      simp only [v_r160, v_r205, hw]
    rw [this]; rfl
  · show Value.bits 32 (v_r161 L g dt) = _
    have hw := wAdd32_smem L 213304 (by decide)
    have ht : (213304 : Int).toNat = 213304 := by decide
    rw [ht] at hw
    have : v_r161 L g dt = BitVec.ofNat 64 ((L.sharedBase + 213304) % 2 ^ 32) := by
      simp only [v_r161, v_r205, hw]
    rw [this]; rfl
  · show Value.bits 32 (v_r162 L g dt) = _
    have hw := wAdd32_smem L 213312 (by decide)
    have ht : (213312 : Int).toNat = 213312 := by decide
    rw [ht] at hw
    have : v_r162 L g dt = BitVec.ofNat 64 ((L.sharedBase + 213312) % 2 ^ 32) := by
      simp only [v_r162, v_r205, hw]
    rw [this]; rfl
  · show Value.bits 32 (v_r163 L g dt) = _
    have hw := wAdd32_smem L 213328 (by decide)
    have ht : (213328 : Int).toNat = 213328 := by decide
    rw [ht] at hw
    have : v_r163 L g dt = BitVec.ofNat 64 ((L.sharedBase + 213328) % 2 ^ 32) := by
      simp only [v_r163, v_r205, hw]
    rw [this]; rfl

/-- The instruction at `pc` is `mbarrier.init` of the object in register `r`, count 1. -/
def isInit (pc r : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨some (_, false), .mbarInit r' o (.imm x)⟩ => r' == r && o == 0 && x == 1
  | _ => false

theorem isInit_spec {pc r : Nat} (h : isInit pc r = true) :
    ∃ p, kernel.code[pc]? = some ⟨some (p, false), .mbarInit r 0 (.imm 1)⟩ := by
  unfold isInit at h
  split at h
  · rename_i p r' o x hc
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    subst h1; subst h2; subst h3
    exact ⟨p, hc⟩
  · cases h

theorem isInit_all : ∀ i < 12, isInit (inSite i).pc (613 + i) = true := by decide +kernel

theorem inLive : ∀ i < 12, 613 + i ∈ Flow.live (inSite i).pc := by decide +kernel

theorem initBar_off_align : ∀ i < 12, (initBar i).off % 8 = 0 := by decide +kernel

theorem initBar_off_lt : ∀ i < 12, (initBar i).off + 8 ≤ 213340 := by decide +kernel

/-- **An mbarrier initialization**: count 1 on the barrier `initBar i` of the thread's CTA. -/
theorem shape_in (hS : SharedOk L) {i : Nat} (hi : i < 12) (hF : Fired L g d e (some u))
    (hs : d.site = inSite i) :
    e = ⟨evPc d.site, .mbInit ((initBar i).loc L (g / L.block)) 1⟩ := by
  obtain ⟨t, ins, h, hinv, hc, hf⟩ := fired_unpack hF
  have hpc : d.site.pc = (inSite i).pc := by rw [hs]
  rw [hpc] at hc hf
  obtain ⟨p, hcode⟩ := isInit_spec (isInit_all i hi)
  obtain rfl := Option.some.inj (hc.symm.trans hcode)
  have hr : t.regs (613 + i) = some (b32 ((L.sharedBase + (initBar i).off) % 2 ^ 32)) := by
    have := reg_at (d := d) (r := 613 + i) h (by rw [hpc]; exact inLive i hi)
    rw [this, val_init L g d.dt i hi]
  have hlt := initBar_off_lt i hi
  have hal := initBar_off_align i hi
  have hmod : (L.sharedBase + (initBar i).off) % 2 ^ 32 = L.sharedBase + (initBar i).off := by
    apply Nat.mod_eq_of_lt
    have := hS.2
    omega
  have := fires_mbInit_at (L := L) (g := g) (t := t) hr (Nat.mod_lt _ (by decide)) (by decide)
    (by decide) (by rw [hmod]; have := hS.1; omega) hf
  rw [this, evPc, hpc, hmod]
  rfl

/-! ### The `expect_tx` arrivals -/

/-- The instruction at `pc` is `mbarrier.arrive.expect_tx` of 65536 bytes on the object in
register `r`, one arrival, release at CTA scope. -/
def isArrive (pc r : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨some (_, false), .mbarArrive r' o (.imm tx) (.imm n) cl rel sc st⟩ =>
    r' == r && o == 0 && tx == 65536 && n == 1 && cl == false && rel == true &&
      decide (sc = .cta) && st.isNone
  | _ => false

theorem isArrive_spec {pc r : Nat} (h : isArrive pc r = true) :
    ∃ p, kernel.code[pc]? = some
      ⟨some (p, false), .mbarArrive r 0 (.imm 65536) (.imm 1) false true .cta none⟩ := by
  unfold isArrive at h
  split at h
  · rename_i p r' o tx n cl rel sc st hc
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Option.isNone_iff_eq_none] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
    subst h1 h2 h3 h4 h5 h6 h7 h8
    exact ⟨p, hc⟩
  · cases h

theorem isArrive_all : ∀ j < 3, isArrive (arrSite j).pc (613 + 2 * j) = true := by decide +kernel

theorem arrLive : ∀ j < 3, 613 + 2 * j ∈ Flow.live (arrSite j).pc := by decide +kernel

theorem initBar_arr (j : Nat) (hj : j < 3) : initBar (2 * j) = kvReadyOf j := by
  interval_cases j <;> rfl

/-- **The `expect_tx` arrival of block `j`**: 65536 bytes, one arrival, release at CTA scope, on
`kv_ready j` of the thread's CTA. -/
theorem shape_arr (hS : SharedOk L) {j : Nat} (hj : j < 3) (hF : Fired L g d e (some u))
    (hs : d.site = arrSite j) :
    e = ⟨evPc d.site, .arrive ((kvReadyOf j).loc L (g / L.block)) 65536 1 true .cta⟩ := by
  obtain ⟨t, ins, h, hinv, hc, hf⟩ := fired_unpack hF
  have hpc : d.site.pc = (arrSite j).pc := by rw [hs]
  rw [hpc] at hc hf
  obtain ⟨p, hcode⟩ := isArrive_spec (isArrive_all j hj)
  obtain rfl := Option.some.inj (hc.symm.trans hcode)
  have hi2 : 2 * j < 12 := by omega
  have hr : t.regs (613 + 2 * j) =
      some (b32 ((L.sharedBase + (kvReadyOf j).off) % 2 ^ 32)) := by
    have := reg_at (d := d) (r := 613 + 2 * j) h (by rw [hpc]; exact arrLive j hj)
    rw [this, val_init L g d.dt (2 * j) hi2, initBar_arr j hj]
  have hlt : (kvReadyOf j).off + 8 ≤ 213340 := Bar.off_lt _
  have hal : (kvReadyOf j).off % 8 = 0 := by
    interval_cases j <;> decide
  have hmod : (L.sharedBase + (kvReadyOf j).off) % 2 ^ 32 = L.sharedBase + (kvReadyOf j).off := by
    apply Nat.mod_eq_of_lt
    have := hS.2
    omega
  have := fires_arrive_at (L := L) (g := g) (t := t) hr (Nat.mod_lt _ (by decide))
    (by rw [hmod]; have := hS.1; omega) (by decide) (by decide) (asms_noWiden _) hf
  rw [this, evPc, hpc, hmod]
  rfl

/-! ### Elections, register request, fences, barriers, broadcasts, shared writes -/

/-- The instruction at `pc` is an unguarded full-mask `elect.sync`. -/
def isElect (pc : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .warp ⟨.elect, none, [_, some _], [], some (.imm x)⟩⟩ => x == -1
  | _ => false

theorem isElect_spec {pc : Nat} (h : isElect pc = true) :
    ∃ dst p, kernel.code[pc]? = some
      ⟨none, .warp ⟨.elect, none, [dst, some p], [], some (.imm (-1))⟩⟩ := by
  unfold isElect at h
  split at h
  · rename_i dst p x hc
    simp only [beq_iff_eq] at h
    subst h
    exact ⟨dst, p, hc⟩
  · cases h

theorem isElect_all : ∀ i < 24, isElect (elSite i).pc = true := by decide +kernel

/-- **An election**: `elect.sync` over the full member mask; the leader is the machine's free
choice (`ProA.next` branches on it). -/
theorem shape_el {i : Nat} (hi : i < 24) (hF : Fired L g d e (some u)) (hs : d.site = elSite i) :
    ∃ inst leader, e = ⟨evPc d.site, .elect 4294967295 inst leader⟩ := by
  obtain ⟨t, ins, h, hinv, hc, hf⟩ := fired_unpack hF
  have hpc : d.site.pc = (elSite i).pc := by rw [hs]
  rw [hpc] at hc hf
  obtain ⟨dst, p, hcode⟩ := isElect_spec (isElect_all i hi)
  obtain rfl := Option.some.inj (hc.symm.trans hcode)
  obtain ⟨inst, leader, he⟩ := fires_elect_full hf
  exact ⟨inst, leader, by rw [he, evPc, hpc]⟩

/-- **The proxy fences**: the async proxy fence on shared memory, after the barrier
initializations (`fnc0`) and after the Q stores (`fnc1`). -/
theorem shape_fnc (hF : Fired L g d e (some u)) (hs : d.site = .fnc0 ∨ d.site = .fnc1) :
    e = ⟨evPc d.site, .fenceProxy (.async (some (.shared .cta))) none⟩ := by
  obtain ⟨t, ins, h, hinv, hc, hf⟩ := fired_unpack hF
  rcases hs with hs | hs
  · have hpc : d.site.pc = 179 := by rw [hs]; rfl
    rw [hpc] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_0)
    rw [fires_fenceProxy_async hf, evPc, hpc]
  · have hpc : d.site.pc = 569 := by rw [hs]; rfl
    rw [hpc] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_1)
    rw [fires_fenceProxy_async hf, evPc, hpc]

/-- **The broadcasts of the warp index**: a full-warp `shfl.sync.idx` of the thread's warp index
from lane 0 (before the copies of block `j`). -/
theorem shape_psh (hF : Fired L g d e (some u))
    (hs : d.site = .psh0 ∨ d.site = .psh1 ∨ d.site = .psh2) :
    ∃ recv ok, e = ⟨evPc d.site, .shfl .idx (b32 (g % L.block / 32)) 0 31 recv ok⟩ := by
  obtain ⟨t, ins, h, hinv, hc, hf⟩ := fired_unpack hF
  have key : ∀ (pc r : Nat) (hp : d.site.pc = pc),
      kernel.code[pc]? = some ⟨none, .warp ⟨.shfl .idx, some (.int .b 32), [some r],
        [.reg 464, .imm 0, .imm 31], some (.imm (-1))⟩⟩ → 464 ∈ Flow.live pc →
      ∃ recv ok, e = ⟨evPc d.site, .shfl .idx (b32 (g % L.block / 32)) 0 31 recv ok⟩ := by
    intro pc r hp hcode hlive
    rw [hp] at hc hf
    obtain rfl := Option.some.inj (hc.symm.trans hcode)
    have hr : t.regs 464 = some (b32 (g % L.block / 32)) := by
      have := reg_at (d := d) (r := 464) h (by rw [hp]; exact hlive)
      rw [this]; rfl
    obtain ⟨av, bv, cv, recv, ok, he, -⟩ := fires_shfl (p := none) hf
    have hsh : Execution.isShfl e = true := by rw [he]; rfl
    obtain ⟨recv', ok', he'⟩ := fires_shfl_idx (p := none) hr hf hsh
    exact ⟨recv', ok', by rw [he', evPc, hp]⟩
  rcases hs with hs | hs | hs
  · exact key 202 _ (by rw [hs]; rfl) Flow.code_shfl_1 (by table_decide)
  · exact key 244 _ (by rw [hs]; rfl) Flow.code_shfl_2 (by table_decide)
  · exact key 286 _ (by rw [hs]; rfl) Flow.code_shfl_3 (by table_decide)

/-- The word `num_pre` the prologue writes (the value of the register it stores). -/
def numPreW (L : Launch) (g : Nat) (dt : Dat) : Value := valueOf L g dt 493

/-- The word `num_iters` the prologue writes. -/
def numItersW (L : Launch) (g : Nat) (dt : Dat) : Value := valueOf L g dt 487

/-- **The role table**: the four bytes of `0x01000202` at `sharedBase + 213336`. -/
theorem shape_st8 (hF : Fired L g d e (some u)) (hs : d.site = .st8) :
    ∃ v', storeValue 32 (b32 16777730) = .ok v' ∧
      e = ⟨evPc d.site, .wr (wordAcc ⟨.shared, g / L.block, (L.sharedBase + 213336) % 2 ^ 32⟩)
        v'.toBytes⟩ := by
  obtain ⟨t, ins, h, hinv, hc, hf⟩ := fired_unpack hF
  have hpc : d.site.pc = 570 := by rw [hs]; rfl
  rw [hpc] at hc hf
  have hins := Option.some.inj (hc.symm.trans (isSymStore_spec
    (by decide +kernel : isSymStore 570 1 213336 [Opnd.imm 16777730] = true)))
  have hop : ins.op = .mem (symStore 1 213336 [Opnd.imm 16777730]) := congrArg Instr.op hins
  have hsub : t.sub = 0 := by
    have h2 := h.2.1
    rw [show sub d = d.site.sub from rfl, hs] at h2
    exact h2
  obtain ⟨v', hsv, he⟩ := fires_st_sym (hf := hf) (j := 0) (hop := hop) (by decide) hsub rfl
    (readValue_imm32 (n := 16777730) (by decide)) rfl (Or.inl rfl)
  refine ⟨v', hsv, ?_⟩
  rw [he, evPc, hpc]
  simp [wordAcc]

/-- **The `(num_pre, num_iters)` write**, word 0: the four bytes of `num_pre` at `sharedBase +
212992`. -/
theorem shape_st9_0 (hF : Fired L g d e (some u)) (hs : d.site = .st9_0) :
    ∃ v', storeValue 32 (numPreW L g d.dt) = .ok v' ∧
      e = ⟨evPc d.site, .wr (wordAcc ⟨.shared, g / L.block, (L.sharedBase + 212992) % 2 ^ 32⟩)
        v'.toBytes⟩ := by
  obtain ⟨t, ins, h, hinv, hc, hf⟩ := fired_unpack hF
  have hpc : d.site.pc = 571 := by rw [hs]; rfl
  have hsub : t.sub = 0 := by
    have h2 := h.2.1
    rw [show sub d = d.site.sub from rfl, hs] at h2
    exact h2
  rw [hpc] at hc hf
  have hins := Option.some.inj (hc.symm.trans (isSymStore_spec
    (by decide +kernel : isSymStore 571 2 212992 [Opnd.reg 493, Opnd.reg 487] = true)))
  have hop : ins.op = .mem (symStore 2 212992 [Opnd.reg 493, Opnd.reg 487]) :=
    congrArg Instr.op hins
  have hr : t.regs 493 = some (numPreW L g d.dt) := by
    have := reg_at (d := d) (r := 493) h (by rw [hpc]; table_decide)
    exact this
  obtain ⟨v', hsv, he⟩ := fires_st_sym (hf := hf) (j := 0) (hop := hop)
    (v := numPreW L g d.dt) (by decide) hsub rfl
    (by simp [readValue, readReg, hr, pure, Except.pure]) rfl (Or.inr (Or.inl rfl))
  refine ⟨v', hsv, ?_⟩
  rw [he, evPc, hpc]
  simp [wordAcc]

/-- **The `(num_pre, num_iters)` write**, word 1: the four bytes of `num_iters` at `sharedBase +
212996`, element 1 of the vector store. -/
theorem shape_st9_1 (hF : Fired L g d e (some u)) (hs : d.site = .st9_1) :
    ∃ v', storeValue 32 (numItersW L g d.dt) = .ok v' ∧
      e = ⟨evPc d.site, .wr (wordAcc ⟨.shared, g / L.block, (L.sharedBase + 212992) % 2 ^ 32 + 4⟩
        1) v'.toBytes⟩ := by
  obtain ⟨t, ins, h, hinv, hc, hf⟩ := fired_unpack hF
  have hpc : d.site.pc = 571 := by rw [hs]; rfl
  have hsub : t.sub = 1 := by
    have h2 := h.2.1
    rw [show sub d = d.site.sub from rfl, hs] at h2
    exact h2
  rw [hpc] at hc hf
  have hins := Option.some.inj (hc.symm.trans (isSymStore_spec
    (by decide +kernel : isSymStore 571 2 212992 [Opnd.reg 493, Opnd.reg 487] = true)))
  have hop : ins.op = .mem (symStore 2 212992 [Opnd.reg 493, Opnd.reg 487]) :=
    congrArg Instr.op hins
  have hr : t.regs 487 = some (numItersW L g d.dt) := by
    have := reg_at (d := d) (r := 487) h (by rw [hpc]; table_decide)
    exact this
  obtain ⟨v', hsv, he⟩ := fires_st_sym (hf := hf) (j := 1) (hop := hop)
    (v := numItersW L g d.dt) (by decide) hsub rfl
    (by simp [readValue, readReg, hr, pure, Except.pure]) rfl (Or.inr (Or.inl rfl))
  refine ⟨v', hsv, ?_⟩
  rw [he, evPc, hpc]
  simp [wordAcc]

/-- **The words written at `sharedBase + 212992`** are `numPre` and `numIters` of the thread's
request and split (`Spec`): `exit_values` of the prologue's table. -/
theorem st9_values {P : Params} {mem0 : Mem0} (hpre : Pre P L mem0) (hg : g < L.threads)
    {dt : Dat} (ha : ArgsOk L g dt.pro) (hs : dt.pro.w71 = P.splits)
    (hm : WordsMatch P (cta L g .z) dt) :
    numPreW L g dt = b32 (numPre P (cta L g .z) (cta L g .x)) ∧
      numItersW L g dt = b32 (P.numIters (cta L g .z) (cta L g .x)) := by
  obtain ⟨-, -, -, -, -, -, h488, h494, -⟩ := exit_values hpre hg ha hs hm
  exact ⟨h494, h488⟩

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
