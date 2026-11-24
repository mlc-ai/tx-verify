-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxQkParity
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxReturnOrigin
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TrackingSoftmaxWriteRegs
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ScoreClosingGate
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0PeerTrace
import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg0BarrierCount
import Lemmas.Protocol.NamedBarSources
import Lemmas.Flow.NotBulk
import Lemmas.Flow.NotClc

@[expose] public section

/-! # Actual CTA barrier identities in the softmax suffix -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking

open PTX PTX.Flow PTX.Proof PTX.EventFrame

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

private structure BarrierLiteral where
  move : Nat
  last : Nat
  reg : Nat
  value : Nat

private def literals (j : Fin 17) : BarrierLiteral :=
  match j.val with
  | 0 => ⟨254, 256, 972, 9⟩
  | 1 => ⟨567, 569, 998, 9⟩
  | 2 => ⟨1152, 1156, 1725, 9⟩
  | 3 => ⟨1340, 1342, 1906, 9⟩
  | 4 => ⟨1500, 1502, 2077, 9⟩
  | 5 => ⟨1658, 1659, 2247, 9⟩
  | 6 => ⟨1815, 1817, 2416, 9⟩
  | 7 => ⟨1833, 1835, 2425, 12⟩
  | 8 => ⟨1834, 1835, 2426, 384⟩
  | 9 => ⟨255, 256, 973, 128⟩
  | 10 => ⟨474, 475, 997, 64⟩
  | 11 => ⟨568, 569, 999, 128⟩
  | 12 => ⟨1153, 1156, 1726, 128⟩
  | 13 => ⟨1341, 1342, 1907, 128⟩
  | 14 => ⟨1501, 1502, 2078, 128⟩
  | 15 => ⟨1518, 1659, 2150, 128⟩
  | _ => ⟨1816, 1817, 2417, 128⟩

private def BarrierLiteral.region (lit : BarrierLiteral) (pc : Nat) : Bool :=
  decide (lit.move < pc ∧ pc ≤ lit.last)

set_option maxRecDepth 100000 in
private theorem literal_audit (j : Fin 17) :
    registerRegionChecked (literals j).reg (literals j).region [(literals j).move] = true := by
  fin_cases j <;> decide +kernel

private theorem literal_local (j : Fin 17) :
    [(literals j).move].all (fun pc => ((kernel.code[pc]?).map (·.op.isLocal)).getD true) =
      true := by
  fin_cases j <;> decide +kernel

private theorem literal_tau {t u : TState} (j : Fin 17)
    (hPc : t.pc = (literals j).move) (hTau : Tau kernel Assumptions.all L g t u) :
    u.regs (literals j).reg = some (b32 (literals j).value) := by
  have hAt : AtVector t (literals j).move [] t.sub t.acc :=
    ⟨hPc, rfl, rfl, tau_fault_free hTau, trivial⟩
  obtain ⟨v, hRun, hv⟩ : ∃ v, run kernel Assumptions.all L g 1 t = some v ∧
      AtVector v ((literals j).move + 1) [((literals j).reg, b32 (literals j).value)]
        t.sub t.acc := by
    fin_cases j <;> seg_fp hAt using norm_bits [literals, b32]
  exact (one_step_matches hTau hRun) ▸ hv.2.2.2.2.1

private def pairRegion (pc : Nat) : Bool := decide (243 ≤ pc ∧ pc ≤ 1841)

set_option maxRecDepth 100000 in
private theorem pair_audit :
    registerRegionChecked 996 pairRegion [160, 207, 242] = true := by decide +kernel

private def BarrierLiterals (t : TState) : Prop :=
  ∀ j : Fin 17, (literals j).region t.pc = true →
    t.regs (literals j).reg = some (b32 (literals j).value)

private theorem literals_tau {t u : TState}
    (hState : BarrierLiterals t) (hTau : Tau kernel Assumptions.all L g t u) :
    BarrierLiterals u :=
  fun j => register_region_tau (property := (· = some (b32 (literals j).value)))
    (literal_audit j) (hState j)
    (fun h _ => literal_tau j (List.mem_singleton.mp h) hTau) hTau

private theorem literals_event {t u : TState} {e : Event}
    (hState : BarrierLiterals t) (he : EStep kernel Assumptions.all L g t e (some u)) :
    BarrierLiterals u :=
  fun j => register_region_event (property := (· = some (b32 (literals j).value)))
    (literal_audit j) (register_updates_local (literal_local j)) (hState j) he

private def BarrierState (L : Launch) (g : Nat) (t : TState) : Prop :=
  softmaxWriteRegion t.pc ∧
    (pairRegion t.pc = true → t.regs 996 = some (b32 (10 + warpOf L g % 2))) ∧
    BarrierLiterals t

private theorem barrier_tau {t u : TState}
    (hState : BarrierState L g t) (hTau : Tau kernel Assumptions.all L g t u) :
    BarrierState L g u := by
  refine ⟨control_region_tau softmax_write_region_closed hState.1 hTau,
    register_region_tau (property := (· = some (b32 (10 + warpOf L g % 2))))
      pair_audit hState.2.1 ?_ hTau, literals_tau hState.2.2 hTau⟩
  intro h
  have hp : t.pc = 160 ∨ t.pc = 207 ∨ t.pc = 242 := by simpa using h
  have hRegion := hState.1
  unfold softmaxWriteRegion at hRegion
  omega

set_option maxRecDepth 100000 in
private theorem barrier_event {t u : TState} {e : Event}
    (hState : BarrierState L g t) (he : EStep kernel Assumptions.all L g t e (some u)) :
    BarrierState L g u :=
  ⟨control_region_event softmax_write_region_closed hState.1 he,
    register_region_event (property := (· = some (b32 (10 + warpOf L g % 2))))
      pair_audit (register_updates_local (by decide +kernel)) hState.2.1 he,
    literals_event hState.2.2 he⟩

private theorem bar_id_of_reg {t : TState} {e : Event} {u : TState}
    {r n id : Nat} {second : Opnd} {c : Option Nat} {mode : BarMode} {align : Bool}
    (hr : t.regs r = some (b32 n)) (hn : n < 16)
    (hf : Fires t.pc (eventTmpl Assumptions.all L g t (.barSyncN (.reg r) second align))
      e (some u)) (he : e.kind = .bar id c mode) : id = n := by
  have hRead := readBits_b32 (L := L) (g := g) hr (by omega)
  have hn' : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [eventTmpl, barTmpl, hRead, hn', not_le.mpr hn, ↓reduceIte] at hf
  cases hSecond : readBits L g t 32 second with
  | error f => simp only [hSecond, Fires, reduceCtorEq, and_false] at hf
  | ok v =>
    simp only [hSecond] at hf
    split at hf
    · exact (Kind.bar.inj (he.symm.trans (congrArg Event.kind hf.1))).1
    · simp [Fires] at hf

private theorem barrier_sites {t : TState} {e : Event} {o : Option TState}
    {ins : Instr} {id : Nat} {count : Option Nat} {mode : BarMode}
    (hRegion : softmaxWriteRegion t.pc) (hc : kernel.code[t.pc]? = some ins)
    (hf : Fires t.pc (eventTmpl Assumptions.all L g t ins.op) e o)
    (hk : e.kind = .bar id count mode) :
    t.pc = 256 ∨ t.pc = 475 ∨ t.pc = 569 ∨ t.pc = 1154 ∨ t.pc = 1156 ∨
      t.pc = 1342 ∨ t.pc = 1502 ∨ t.pc = 1659 ∨ t.pc = 1817 ∨ t.pc = 1835 := by
  have hAudit : OpPcsFast kernel.code barOp
      [97, 256, 475, 569, 1154, 1156, 1342, 1502, 1659, 1817, 1835,
        2160, 2330, 2585, 2604, 3610] = true := by decide +kernel
  have hMem := OpPcsFast.mem hAudit hc (fires_bar_op hf hk)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
  unfold softmaxWriteRegion at hRegion
  omega

section
variable {t u : TState}

private theorem closing_from_literals {e : Event} (hpre : Pre P L mem0) (hp : t.pc = 1835)
    (hRegs : BarrierLiterals t) (he : EStep kernel Assumptions.all L g t e (some u)) :
    e.kind = .bar 12 none .sync := by
  obtain ⟨ins, hc, _, hf⟩ := estep_event_source he
  rw [hp] at hc
  obtain rfl := Option.some.inj (Flow.code_1835.symm.trans hc)
  have hId : t.regs 2425 = some (b32 12) := hRegs 7 (by rw [hp]; decide)
  have hCount : t.regs 2426 = some (b32 384) := hRegs 8 (by rw [hp]; decide)
  have hA := readBits_b32 (L := L) (g := g) hId (by decide)
  have hN := readBits_b32 (L := L) (g := g) hCount (by decide)
  have ht : eventTmpl Assumptions.all L g t (.barSyncN (.reg 2425) (.reg 2426) false) =
      .bar 12 (PTX.next t) none .sync := by
    simp [eventTmpl, barTmpl, hA, hN, hpre.block]
  rw [ht] at hf
  exact congrArg Event.kind hf.1

/-- A continuing event at the softmax gate is its full-CTA synchronization. -/
theorem softmax_gate_at_site {i : Nat} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (he : X.get (g, i) = some e) (hTag : e.pc = 1835) (hLater : i + 1 < (X.tr g).length) :
    e.kind = .bar 12 none .sync := by
  obtain ⟨o, hRun⟩ := hX.thr g (Frame.lt_of_get hX he)
  have hInitial : BarrierLiterals ({} : TState) := by
    intro j h
    have hNo : (literals j).region 0 = false := by fin_cases j <;> decide
    rw [hNo] at h
    cases h
  obtain ⟨v, continuation, hRegs, hStep⟩ := actual_event_invariant literals_tau literals_event
    hInitial hRun (List.mem_of_getElem? he)
  cases continuation with
  | none =>
    obtain ⟨_, _, hf⟩ := hStep
    have hEnd := Flow.Run.end_last hRun he (fires_none_ends hf)
    omega
  | some u => exact closing_from_literals hpre ((estep_source_pc hStep).symm.trans hTag) hRegs hStep

private theorem wg0_closing_from_state {e : Event} {count : Option Nat} {mode : BarMode}
    (hpre : Pre P L mem0) (hState : BarrierState L g t)
    (he : EStep kernel Assumptions.all L g t e (some u)) (hk : e.kind = .bar 12 count mode) :
    t.pc = 1835 ∧ count = none ∧ mode = .sync := by
  obtain ⟨ins, hc, _, hf⟩ := estep_event_source he
  have hSites := barrier_sites hState.1 hc hf hk
  have noNine (j : Fin 17) {a : Nat} {b : Opnd} {al : Bool}
      (hReg : (literals j).reg = a) (hVal : (literals j).value = 9)
      (hIn : (literals j).region t.pc = true) (hop : ins.op = .barSyncN (.reg a) b al) :
      False := by
    have hr := hState.2.2 j hIn
    rw [hReg, hVal] at hr
    rw [hop] at hf
    exact (by decide : ¬ (12 : Nat) = 9) (bar_id_of_reg hr (by decide) hf hk)
  rcases hSites with hp | hp | hp | hp | hp | hp | hp | hp | hp | hp <;> rw [hp] at hc
  · obtain rfl := Option.some.inj (Flow.code_256.symm.trans hc)
    exact (noNine 0 rfl rfl (by rw [hp]; decide) rfl).elim
  · obtain rfl := Option.some.inj (Flow.code_475.symm.trans hc)
    have hr := hState.2.1 (by rw [hp]; decide)
    have hId := bar_id_of_reg hr (by omega) hf hk
    omega
  · obtain rfl := Option.some.inj (Flow.code_569.symm.trans hc)
    exact (noNine 1 rfl rfl (by rw [hp]; decide) rfl).elim
  · obtain rfl := Option.some.inj (Flow.code_1154.symm.trans hc)
    exact (noNine 2 rfl rfl (by rw [hp]; decide) rfl).elim
  · obtain rfl := Option.some.inj (Flow.code_1156.symm.trans hc)
    exact (noNine 2 rfl rfl (by rw [hp]; decide) rfl).elim
  · obtain rfl := Option.some.inj (Flow.code_1342.symm.trans hc)
    exact (noNine 3 rfl rfl (by rw [hp]; decide) rfl).elim
  · obtain rfl := Option.some.inj (Flow.code_1502.symm.trans hc)
    exact (noNine 4 rfl rfl (by rw [hp]; decide) rfl).elim
  · obtain rfl := Option.some.inj (Flow.code_1659.symm.trans hc)
    exact (noNine 5 rfl rfl (by rw [hp]; decide) rfl).elim
  · obtain rfl := Option.some.inj (Flow.code_1817.symm.trans hc)
    exact (noNine 6 rfl rfl (by rw [hp]; decide) rfl).elim
  · exact ⟨hp, (Kind.bar.inj (hk.symm.trans (closing_from_literals hpre hp hState.2.2 he))).2⟩

private theorem barrier_run_from_anchor {start : Nat}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hg : g < L.threads) (hFirst : FirstMaskAnchor P L X g start)
    (hEvents : (X.tr g).drop start ≠ []) :
    ∃ t o, t.pc = 264 ∧ BarrierState L g t ∧
      Run kernel Assumptions.all L g t ((X.tr g).drop start) o := by
  obtain ⟨d, hSite, _, hAnchor⟩ := hFirst
  obtain ⟨t, o, hGood, hRun⟩ := actual_suffix_from_followed hX hg (hs g hg) hAnchor hEvents
  have hAt : (Wg0.code P L g).AtD d t := hGood.1
  have hPc : t.pc = 264 := by
    have h := hAt.1
    change t.pc = d.site.pc at h
    rw [hSite] at h
    exact h
  have hPair := Wg0.reg_value hAt (r := 996) (by
    rw [hSite]
    decide +kernel)
  have hStart : BarrierState L g t := by
    refine ⟨by rw [hPc]; decide, fun _ => ?_, ?_⟩
    · simpa [Wg0.valueOf, Wg0.table, lookupLit] using hPair
    · intro j h
      rw [hPc] at h
      have hNo : (literals j).region 264 = false := by fin_cases j <;> decide
      rw [hNo] at h
      cases h
  exact ⟨t, o, hPc, hStart, hRun⟩

private theorem barrier_state_from_anchor {start i : Nat} {e : Event}
    (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e) (hLe : start ≤ i)
    (hFirst : FirstMaskAnchor P L X g start) :
    ∃ t o, BarrierState L g t ∧ EStep kernel Assumptions.all L g t e o := by
  have hGet : ((X.tr g).drop start)[i - start]? = some e := by
    rw [List.getElem?_drop, Nat.add_sub_of_le hLe]
    exact he
  have hm := List.mem_of_getElem? hGet
  have hg := Frame.lt_of_get hX he
  obtain ⟨t, o, _, hStart, hRun⟩ :=
    barrier_run_from_anchor hX hs hg hFirst (List.ne_nil_of_mem hm)
  exact actual_event_invariant barrier_tau barrier_event hStart hRun hm

private theorem dismissed_barrier_state {i tag id : Nat} {count : Option Nat} {mode : BarMode}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some ⟨tag, .bar id count mode⟩)
    (hDismiss : Frame.stateAt (Machine.code P L) X g i = some none) :
    wgOf L g = 0 ∧ ∃ t u, BarrierState L g t ∧
      EStep kernel Assumptions.all L g t ⟨tag, .bar id count mode⟩ (some u) := by
  obtain ⟨start, hLe, d, hSite, hZero, hAnchor⟩ :=
    mask_anchor_after_dismissal hpre hX hs he hDismiss
  have hg := Frame.lt_of_get hX he
  obtain ⟨v, q, hv, hStep⟩ :=
    barrier_state_from_anchor hX hs he hLe ⟨d, hSite, hZero, hAnchor⟩
  cases q with
  | none =>
    obtain ⟨_, _, hf⟩ := hStep
    have hEnd := fires_none_ends hf
    simp [Ends] at hEnd
  | some u =>
    exact ⟨RingRoleGeometry.of_trace hX hg (hs g hg).machine hAnchor, v, u, hv, hStep⟩

/-- Any actual barrier 12 after softmax tracking has been dismissed is its full CTA gate. -/
theorem dismissed_softmax_closing {i tag : Nat} {count : Option Nat} {mode : BarMode}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some ⟨tag, .bar 12 count mode⟩)
    (hDismiss : Frame.stateAt (Machine.code P L) X g i = some none) :
    tag = 1835 ∧ count = none ∧ mode = .sync := by
  obtain ⟨_, t, u, hv, hStep⟩ := dismissed_barrier_state hpre hX hs he hDismiss
  obtain ⟨hp, hCount, hMode⟩ := wg0_closing_from_state hpre hv hStep rfl
  exact ⟨(estep_source_pc hStep).trans hp, hCount, hMode⟩

private theorem bar_of_operands {e : Event} {id n ra rb : Nat} {align : Bool} (hpre : Pre P L mem0)
    (hId : t.regs ra = some (b32 id)) (hCount : t.regs rb = some (b32 n)) (hIdLt : id < 16)
    (hn : n = 64 ∨ n = 128)
    (hf : Fires t.pc (eventTmpl Assumptions.all L g t (.barSyncN (.reg ra) (.reg rb) align))
      e (some u)) : e.kind = .bar id (some n) .sync := by
  rcases hn with rfl | rfl <;>
    exact congrArg Event.kind (fires_barTmpl_at (readBits_b32 (L := L) (g := g) hId (by omega))
      (readBits_b32 (by exact hCount) (by decide)) hIdLt
      (by decide) (by decide) (by decide) (by rw [hpre.block]; decide) hf)

/-- At the exchange barrier's instruction the recorded event has the pair operands. -/
theorem softmax_pair_at_site {i start : Nat} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hAnchor : FirstMaskAnchor P L X g start) (hBefore : start ≤ i)
    (he : X.get (g, i) = some e) (hTag : e.pc = 475) (hLater : i + 1 < (X.tr g).length) :
    e.kind = .bar (10 + warpOf L g % 2) (some 64) .sync := by
  obtain ⟨t, o, hState, hStep⟩ := barrier_state_from_anchor hX hs he hBefore hAnchor
  cases o with
  | none =>
    obtain ⟨_, _, hf⟩ := hStep
    obtain ⟨_, hRun⟩ := hX.thr g (Frame.lt_of_get hX he)
    have hEnd := Flow.Run.end_last hRun he (fires_none_ends hf)
    omega
  | some u =>
    have hp : t.pc = 475 := (estep_source_pc hStep).symm.trans hTag
    obtain ⟨ins, hc, _, hf⟩ := estep_event_source hStep
    rw [hp] at hc
    obtain rfl := Option.some.inj (Flow.code_475.symm.trans hc)
    exact bar_of_operands hpre (hState.2.1 (by rw [hp]; decide))
      (hState.2.2 10 (by rw [hp]; decide)) (by omega) (.inl rfl) hf

private theorem bar9_from_literals {e : Event} (hpre : Pre P L mem0) (hState : BarrierState L g t)
    (he : EStep kernel Assumptions.all L g t e (some u))
    (hSites : t.pc = 256 ∨ t.pc = 569 ∨ t.pc = 1154 ∨ t.pc = 1156 ∨
      t.pc = 1342 ∨ t.pc = 1502 ∨ t.pc = 1659 ∨ t.pc = 1817) :
    e.kind = .bar 9 (some 128) .sync := by
  obtain ⟨ins, hc, _, hf⟩ := estep_event_source he
  have bar9 (j k : Fin 17) {ra rb : Nat}
      (ha : (literals j).reg = ra) (hb : (literals k).reg = rb)
      (hA : (literals j).value = 9) (hB : (literals k).value = 128)
      (hInA : (literals j).region t.pc = true) (hInB : (literals k).region t.pc = true)
      {al : Bool}
      (hFire : Fires t.pc (eventTmpl Assumptions.all L g t (.barSyncN (.reg ra) (.reg rb) al))
        e (some u)) : e.kind = .bar 9 (some 128) .sync := by
    have ha' := hState.2.2 j hInA
    have hb' := hState.2.2 k hInB
    rw [ha, hA] at ha'
    rw [hb, hB] at hb'
    exact bar_of_operands hpre ha' hb' (by decide) (.inr rfl) hFire
  rcases hSites with hp | hp | hp | hp | hp | hp | hp | hp <;> rw [hp] at hc
  · obtain rfl := Option.some.inj (Flow.code_256.symm.trans hc)
    exact bar9 0 9 rfl rfl rfl rfl (by rw [hp]; decide) (by rw [hp]; decide) hf
  · obtain rfl := Option.some.inj (Flow.code_569.symm.trans hc)
    exact bar9 1 11 rfl rfl rfl rfl (by rw [hp]; decide) (by rw [hp]; decide) hf
  · obtain rfl := Option.some.inj (Flow.code_1154.symm.trans hc)
    exact bar9 2 12 rfl rfl rfl rfl (by rw [hp]; decide) (by rw [hp]; decide) hf
  · obtain rfl := Option.some.inj (Flow.code_1156.symm.trans hc)
    exact bar9 2 12 rfl rfl rfl rfl (by rw [hp]; decide) (by rw [hp]; decide) hf
  · obtain rfl := Option.some.inj (Flow.code_1342.symm.trans hc)
    exact bar9 3 13 rfl rfl rfl rfl (by rw [hp]; decide) (by rw [hp]; decide) hf
  · obtain rfl := Option.some.inj (Flow.code_1502.symm.trans hc)
    exact bar9 4 14 rfl rfl rfl rfl (by rw [hp]; decide) (by rw [hp]; decide) hf
  · obtain rfl := Option.some.inj (Flow.code_1659.symm.trans hc)
    exact bar9 5 15 rfl rfl rfl rfl (by rw [hp]; decide) (by rw [hp]; decide) hf
  · obtain rfl := Option.some.inj (Flow.code_1817.symm.trans hc)
    exact bar9 6 16 rfl rfl rfl rfl (by rw [hp]; decide) (by rw [hp]; decide) hf

private theorem softmax_barrier_kind {e : Event} {id : Nat} {count : Option Nat} {mode : BarMode}
    (hpre : Pre P L mem0) (hState : BarrierState L g t)
    (he : EStep kernel Assumptions.all L g t e (some u)) (hk : e.kind = .bar id count mode) :
    e.kind = .bar 9 (some 128) .sync ∨
      e.kind = .bar (10 + warpOf L g % 2) (some 64) .sync ∨
      e.kind = .bar 12 none .sync := by
  obtain ⟨_, hc, _, hf⟩ := estep_event_source he
  have hSites := barrier_sites hState.1 hc hf hk
  by_cases hp : t.pc = 475
  · rw [hp] at hc
    obtain rfl := Option.some.inj (Flow.code_475.symm.trans hc)
    exact .inr (.inl (bar_of_operands hpre (hState.2.1 (by rw [hp]; decide))
      (hState.2.2 10 (by rw [hp]; decide)) (by omega) (.inl rfl) hf))
  by_cases hClose : t.pc = 1835
  · exact .inr (.inr (closing_from_literals hpre hClose hState.2.2 he))
  exact .inl (bar9_from_literals hpre hState he (by omega))

/-- The barrier 9 instruction tags used to count the body and the LSE handoff. -/
def softmaxBodyBar9 (e : Event) : Bool :=
  e.pc == 256 || e.pc == 569 || e.pc == 1154 || e.pc == 1156

/-- The recorded softmax body barriers use the whole warpgroup. -/
theorem softmax_bar9_at_site {i start : Nat} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (hAnchor : FirstMaskAnchor P L X g start) (hBefore : start ≤ i)
    (he : X.get (g, i) = some e) (hTag : softmaxBodyBar9 e = true)
    (hLater : i + 1 < (X.tr g).length) : e.kind = .bar 9 (some 128) .sync := by
  obtain ⟨t, o, hState, hStep⟩ := barrier_state_from_anchor hX hs he hBefore hAnchor
  have hPc := estep_source_pc hStep
  simp only [softmaxBodyBar9, Bool.or_eq_true, beq_iff_eq, hPc] at hTag
  cases o with
  | none =>
    obtain ⟨_, _, hf⟩ := hStep
    obtain ⟨_, hRun⟩ := hX.thr g (Frame.lt_of_get hX he)
    have hEnd := Flow.Run.end_last hRun he (fires_none_ends hf)
    omega
  | some u => exact bar9_from_literals hpre hState hStep (by omega)

/-- Actual arrivals on the softmax-wide barrier are syncs with 128 participants. -/
theorem actual_bar9 {i tag : Nat} {count : Option Nat} {mode : BarMode}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some ⟨tag, .bar 9 count mode⟩) :
    warpOf L g < 4 ∧ count = some 128 ∧ mode = .sync := by
  have hg := Frame.lt_of_get hX he
  by_cases hDismiss : Frame.stateAt (Machine.code P L) X g i = some none
  · obtain ⟨hWg, t, u, hState, hStep⟩ := dismissed_barrier_state hpre hX hs he hDismiss
    refine ⟨?_, ?_⟩
    · unfold warpOf wgOf at *
      omega
    rcases softmax_barrier_kind hpre hState hStep rfl with h | h | h
    · exact (Kind.bar.inj h).2
    · have hh := (Kind.bar.inj h).1
      omega
    · cases h
  · obtain ⟨d, _, _, hf⟩ :=
      RingSourceSites.fired_at_followed hX (hs g hg).machine hDismiss he (by simp)
    obtain ⟨_, _, _, hw, hc, hm⟩ := Wg0BarrierTrace.bar9_fired hpre hf rfl
    exact ⟨hw, hc, hm⟩

/-- Actual arrivals on a peer barrier are syncs with its 64 participant lanes. -/
theorem actual_pair_bar {i tag : Nat} {p : Fin 2} {count : Option Nat} {mode : BarMode}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some ⟨tag, .bar (10 + p.val) count mode⟩) :
    warpOf L g < 4 ∧ warpOf L g % 2 = p.val ∧ count = some 64 ∧ mode = .sync := by
  have hg := Frame.lt_of_get hX he
  have hp := p.isLt
  by_cases hDismiss : Frame.stateAt (Machine.code P L) X g i = some none
  · obtain ⟨hWg, t, u, hState, hStep⟩ := dismissed_barrier_state hpre hX hs he hDismiss
    refine ⟨?_, ?_⟩
    · unfold warpOf wgOf at *
      omega
    rcases softmax_barrier_kind hpre hState hStep rfl with h | h | h
    · have hh := (Kind.bar.inj h).1
      omega
    · obtain ⟨hi, hc, hm⟩ := Kind.bar.inj h
      exact ⟨by omega, hc, hm⟩
    · have hh := (Kind.bar.inj h).1
      omega
  · obtain ⟨d, _, _, hf⟩ :=
      RingSourceSites.fired_at_followed hX (hs g hg).machine hDismiss he (by simp)
    obtain ⟨_, _, _, hw, hp, hc, hm⟩ := Wg0PeerTrace.pair_fired (p := p) hpre hf rfl
    exact ⟨hw, hp, hc, hm⟩

/-- Relative count of warpgroup and pair barriers at a concrete softmax position. -/
private def barrierBalance (pc : Nat) : Int :=
  if pc ≤ 256 then 0
  else if pc ≤ 475 then 1
  else if pc ≤ 569 then -1
  else if pc ≤ 1154 then 0
  else if pc ≤ 1156 then 1
  else if pc ≤ 1342 then 2
  else if pc ≤ 1502 then 3
  else if pc ≤ 1659 then 4
  else if pc ≤ 1817 then 5
  else 6

private def changesBalance (pc : Nat) : Bool :=
  pc == 256 || pc == 475 || pc == 569 || pc == 1154 || pc == 1156 ||
    pc == 1342 || pc == 1502 || pc == 1659 || pc == 1817

private def balanceStepChecked (pc : Nat) (ins : Instr) : Bool :=
  if changesBalance pc then ins.guard.isNone && !ins.op.isLocal
  else closesControlRegion (fun dest => barrierBalance dest = barrierBalance pc) pc ins

set_option maxRecDepth 100000 in
private theorem balance_step_audit :
    kernel.code.zipIdx.all (fun (ins, pc) =>
      !decide (softmaxWriteRegion pc) || balanceStepChecked pc ins) = true := by
  decide +kernel

private theorem balance_checked {t : TState} {ins : Instr}
    (hRegion : softmaxWriteRegion t.pc) (hCode : kernel.code[t.pc]? = some ins) :
    balanceStepChecked t.pc ins = true := by
  have h := List.all_eq_true.mp balance_step_audit (ins, t.pc)
    (List.mem_zipIdx_iff_getElem?.mpr hCode)
  simpa only [decide_eq_true hRegion, Bool.not_true, Bool.false_or] using h

private theorem balance_tau (hRegion : softmaxWriteRegion t.pc)
    (hu : Tau kernel Assumptions.all L g t u) :
    barrierBalance u.pc = barrierBalance t.pc := by
  unfold Tau out at hu
  split at hu
  · cases hu
  split at hu
  · cases hu
  rename_i ins hCode
  have hChecked := balance_checked hRegion hCode
  by_cases hChange : changesBalance t.pc = true
  · obtain ⟨hGuard, hLocal⟩ : ins.guard = none ∧ ins.op.isLocal = false := by
      simpa [balanceStepChecked, hChange, Option.isNone_iff_eq_none] using hChecked
    rw [hGuard] at hu
    simp [guardHolds, hLocal, pure, Except.pure] at hu
  · have hKeep : closesControlRegion (fun dest => barrierBalance dest = barrierBalance t.pc)
        t.pc ins = true := by simpa [balanceStepChecked, hChange] using hChecked
    split at hu
    · cases hu
    · rename_i hGuard
      cases hu
      apply control_fallthrough hKeep
      cases hins : ins.guard
      · simp [hins, guardHolds, pure, Except.pure] at hGuard
      · rfl
    split at hu
    · split at hu
      · rename_i v h
        cases hu
        exact control_local_step rfl hKeep (local_frame h)
      · cases hu
    · cases hu

theorem bar_tag_return {e : Event} {id : Nat} {count : Option Nat} {mode : BarMode}
    (he : EStep kernel Assumptions.all L g t e (some u)) (hk : e.kind = .bar id count mode) :
    u.pc = t.pc + 1 := by
  obtain ⟨ins, _, _, hf⟩ := estep_event_source he
  have ho := fires_bar_op hf hk
  cases hop : ins.op <;> simp only [hop, barOp, Bool.false_eq_true] at ho
  all_goals
    rw [hop] at hf
    simp only [eventTmpl, barTmpl] at hf
    repeat' split at hf
    all_goals first
      | (rw [Option.some.inj hf.2]; rfl)
      | (have hNone : some u = none := hf.2; cases hNone)

private theorem tag_not_counted {e : Event} (hpre : Pre P L mem0) (hState : BarrierState L g t)
    (he : EStep kernel Assumptions.all L g t e (some u)) (hKeep : changesBalance t.pc = false) :
    Execution.isBarId 9 e = false ∧ Execution.isBarId (10 + warpOf L g % 2) e = false := by
  have hTag (id : Nat) (hId : id < 12) : Execution.isBarId id e = false := by
    apply Bool.eq_false_iff.mpr
    intro hb
    obtain ⟨_, _, _, hk⟩ := NamedBar.isBarId_form hb
    have hKind := congrArg Event.kind hk
    obtain ⟨_, hCode, _, hf⟩ := estep_event_source he
    have hSites := barrier_sites hState.1 hCode hf hKind
    have hClose : t.pc = 1835 := by
      simp only [changesBalance, Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hKeep
      omega
    have hid := (Kind.bar.inj (hKind.symm.trans (closing_from_literals hpre hClose
      hState.2.2 he))).1
    omega
  exact ⟨hTag _ (by decide), hTag _ (by omega)⟩

private def countBalance (L : Launch) (g : Nat) (before : List Event) : Int :=
  (before.countP (Execution.isBarId 9) : Int) -
    2 * (before.countP (Execution.isBarId (10 + warpOf L g % 2)) : Int)

private theorem balance_event {e : Event} (hpre : Pre P L mem0) (hState : BarrierState L g t)
    (he : EStep kernel Assumptions.all L g t e (some u)) :
    barrierBalance u.pc = barrierBalance t.pc + countBalance L g [e] := by
  obtain ⟨ins, hCode, hLocal, hf⟩ := estep_event_source he
  cases hTag : changesBalance t.pc
  · obtain ⟨hNine, hPair⟩ := tag_not_counted hpre hState he hTag
    have hKeep : closesControlRegion (fun dest => barrierBalance dest = barrierBalance t.pc)
        t.pc ins = true := by
      simpa [balanceStepChecked, hTag] using balance_checked hState.1 hCode
    have hEq : barrierBalance u.pc = barrierBalance t.pc := by
      rcases (estep_return_pc he (fun _ _ _ h => local_frame h)).2 with h | h
      · rw [h]
      · rw [h]
        cases hop : ins.op <;>
          simp only [hop, closesControlRegion, Bool.and_eq_true, decide_eq_true_eq] at hKeep
        case bra dst uni =>
          rw [hop] at hLocal
          cases hLocal
        all_goals first | exact hKeep.1 | exact hKeep
    simpa [countBalance, hNine, hPair] using hEq
  · have hSites : t.pc = 256 ∨ t.pc = 475 ∨ t.pc = 569 ∨ t.pc = 1154 ∨ t.pc = 1156 ∨
        t.pc = 1342 ∨ t.pc = 1502 ∨ t.pc = 1659 ∨ t.pc = 1817 := by
      simpa [changesBalance, or_assoc] using hTag
    by_cases hp : t.pc = 475
    · rw [hp] at hCode
      obtain rfl := Option.some.inj (Flow.code_475.symm.trans hCode)
      have hk := bar_of_operands hpre (hState.2.1 (by rw [hp]; decide))
        (hState.2.2 10 (by rw [hp]; decide)) (by omega) (.inl rfl) hf
      have hNext := bar_tag_return he hk
      rw [hNext, hp]
      simp [barrierBalance, countBalance, Execution.isBarId, hk,
        show 10 + warpOf L g % 2 ≠ 9 by omega]
    · have hk := bar9_from_literals hpre hState he (by omega)
      have hNext := bar_tag_return he hk
      rw [hNext]
      have hId : ¬ (9 = 10 + warpOf L g % 2) := by omega
      simp [countBalance, Execution.isBarId, hk, hId]
      rcases hSites with h | h | h | h | h | h | h | h | h
      all_goals first | exact (hp h).elim | (rw [h]; decide)

private theorem balance_local_path (hState : BarrierState L g t)
    (hPath : Relation.ReflTransGen (Tau kernel Assumptions.all L g) t u) :
    BarrierState L g u ∧ barrierBalance u.pc = barrierBalance t.pc := by
  induction hPath with
  | refl => exact ⟨hState, rfl⟩
  | tail _ h ih => exact ⟨barrier_tau ih.1 h, (balance_tau ih.1.1 h).trans ih.2⟩
end

private theorem balance_trace {t : TState} {e : Event} {before tail : List Event}
    {o : Option TState}
    (hpre : Pre P L mem0) (hState : BarrierState L g t)
    (hRun : Run kernel Assumptions.all L g t (before ++ e :: tail) o) :
    barrierBalance e.pc = barrierBalance t.pc + countBalance L g before := by
  induction before generalizing t with
  | nil =>
    change Run kernel Assumptions.all L g t (e :: tail) o at hRun
    cases hRun with
    | step hLocal hEvent _ =>
      rw [estep_source_pc hEvent, (balance_local_path hState hLocal).2]
      simp [countBalance]
    | last hLocal hEvent =>
      rw [estep_source_pc hEvent, (balance_local_path hState hLocal).2]
      simp [countBalance]
  | cons f before ih =>
    change Run kernel Assumptions.all L g t (f :: (before ++ e :: tail)) o at hRun
    generalize hs : f :: (before ++ e :: tail) = events at hRun
    cases hRun with
    | nil => cases hs
    | step hLocal hEvent hTail =>
      obtain ⟨rfl, rfl⟩ := List.cons.inj hs
      obtain ⟨hAt, hEq⟩ := balance_local_path hState hLocal
      rw [ih (barrier_event hAt hEvent) hTail, balance_event hpre hAt hEvent, hEq]
      simp only [countBalance, List.countP_cons, List.countP_nil, Nat.zero_add, Int.natCast_add]
      omega
    | last =>
      have hs := (List.cons.inj hs).2
      simp at hs

private theorem barrier_balance_of_suffix {start i : Nat} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e) (hLe : start ≤ i)
    (hFirst : FirstMaskAnchor P L X g start) :
    countBalance L g ((X.tr g).take i) = barrierBalance e.pc := by
  let events := (X.tr g).drop start
  let k := i - start
  have hGet : events[k]? = some e := by
    change ((X.tr g).drop start)[i - start]? = _
    rw [List.getElem?_drop, Nat.add_sub_of_le hLe]
    exact he
  have hg := Frame.lt_of_get hX he
  have hLength : start < (X.tr g).length := hLe.trans_lt (PTX.len_of_get he)
  have hGetStart : X.get (g, start) = some ((X.tr g)[start]'hLength) :=
    List.getElem?_eq_getElem hLength
  obtain ⟨t, o, hp, hInit, hRun⟩ := barrier_run_from_anchor hX hs hg hFirst
    (List.ne_nil_of_mem (List.mem_of_getElem? hGet))
  obtain ⟨d, hSite, hBlock, hState⟩ := hFirst
  have hPair := Wg0PeerTrace.count_at_wg0 hpre hX (hs g hg).machine hGetStart hState
  have hNine := Wg0BarrierCount.count_at_wg0 hpre hX (hs g hg).machine hGetStart hState
  rw [Wg0PeerTrace.ordinal, hSite, hBlock] at hPair
  change ((X.tr g).take start).countP (Execution.isBarId (10 + warpOf L g % 2)) = 0 at hPair
  rw [Wg0BarrierCount.ordinal, hSite, hBlock] at hNine
  change ((X.tr g).take start).countP (Execution.isBarId 9) = 1 at hNine
  have hCut : events = events.take k ++ e :: events.drop (k + 1) := by
    have hDrop := List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp hGet).1
    rw [(List.getElem?_eq_some_iff.mp hGet).2] at hDrop
    rw [← hDrop]
    exact (List.take_append_drop ..).symm
  change Run kernel Assumptions.all L g t events o at hRun
  rw [hCut] at hRun
  have hBalance := balance_trace hpre hInit hRun
  rw [hp] at hBalance
  change barrierBalance e.pc = 1 + countBalance L g (events.take k) at hBalance
  have hTake : (X.tr g).take i = (X.tr g).take start ++ events.take k := by
    dsimp only [events, k]
    rw [← List.take_add, Nat.add_sub_of_le hLe]
  rw [hTake, countBalance, List.countP_append, List.countP_append, hNine, hPair]
  simp only [Nat.zero_add, Int.natCast_add] at *
  unfold countBalance at hBalance
  omega

/-- The exchange write happens after its block's opening barrier and before its pair barrier. -/
theorem actual_exchange_barrier_counts {start i : Nat} {e : Event} {j : Fin 8}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e) (hLe : start ≤ i) (hFirst : FirstMaskAnchor P L X g start)
    (hTag : e.pc = (Wg0.Site.exchStore j).pc) :
    ((X.tr g).take i).countP (Execution.isBarId 9) =
      2 * ((X.tr g).take i).countP (Execution.isBarId (10 + warpOf L g % 2)) + 1 := by
  have h := barrier_balance_of_suffix hpre hX hs he hLe hFirst
  rw [hTag] at h
  have hp : barrierBalance (Wg0.Site.exchStore j).pc = 1 := by fin_cases j <;> decide
  rw [hp] at h
  unfold countBalance at h
  omega

/-- The probability write happens after both warpgroup barriers of its block. -/
theorem actual_probability_barrier_counts {start i : Nat} {e : Event} {j : Fin 4}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e) (hLe : start ≤ i) (hFirst : FirstMaskAnchor P L X g start)
    (hTag : e.pc = (Wg0.Site.pStore j).pc) :
    ((X.tr g).take i).countP (Execution.isBarId 9) =
      2 * ((X.tr g).take i).countP (Execution.isBarId (10 + warpOf L g % 2)) := by
  have h := barrier_balance_of_suffix hpre hX hs he hLe hFirst
  rw [hTag] at h
  have hp : barrierBalance (Wg0.Site.pStore j).pc = 0 := by fin_cases j <;> decide
  rw [hp] at h
  unfold countBalance at h
  omega

/-- The row maximum and the later half sum both occupy odd warpgroup ordinals. -/
theorem actual_row_write_barrier_counts {start i : Nat} {e : Event}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ h < L.threads, (Machine.code P L h).Sound)
    (he : X.get (g, i) = some e) (hLe : start ≤ i) (hFirst : FirstMaskAnchor P L X g start)
    (hTag : e.pc = Wg0.Site.rowMax.pc ∨ e.pc = Wg0.Site.lseStore0.pc) :
    ∃ m, ((X.tr g).take i).countP (Execution.isBarId 9) = 2 * m + 1 := by
  have h := barrier_balance_of_suffix hpre hX hs he hLe hFirst
  let n := ((X.tr g).take i).countP (Execution.isBarId 9)
  refine ⟨n / 2, ?_⟩
  unfold countBalance at h
  change n = _
  rcases hTag with hTag | hTag
  · rw [hTag, show barrierBalance Wg0.Site.rowMax.pc = -1 from rfl] at h
    change (n : Int) - _ = -1 at h
    omega
  · rw [hTag, show barrierBalance Wg0.Site.lseStore0.pc = 1 from rfl] at h
    change (n : Int) - _ = 1 at h
    omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.MachineTracking
