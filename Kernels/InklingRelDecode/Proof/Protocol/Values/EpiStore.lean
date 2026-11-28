-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Protocol.Values.EpiWin
import Kernels.InklingRelDecode.Proof.Lib.EvLane
import Kernels.InklingRelDecode.Proof.Lib.MoveStep
import Kernels.InklingRelDecode.Flow.Code.Part040
import Lemmas.Flow.OutUnpack
import Lemmas.Flow.StoreAdvance
import Lemmas.Flow.StoreSrc
import Lemmas.Flow.StoreGlobal

@[expose] public section

/-! # The words the epilogue stores

The unpack at pc `2750 + 3 q` splits the pair in register `2479 + q` into the registers
`1832 + 2 q` and `1833 + 2 q`; the stores at `2751 + 3 q` and `2752 + 3 q` write them. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
open PTX PTX.Flow PTX.Proof PTX.Kernels.InklingRelDecode.Proof.Lib

noncomputable section
variable {L : Launch} {g : Nat} {X : Execution}

/-- The word `j` of the row: zero when the launch has no block, else the product. -/
def wordV (b : Bool) (s : ℝ) (o : Nat → ℝ) (j : Nat) : Value :=
  if b then b32 0 else .float .f32 (s * o j)

theorem split_pair (b : Bool) (s : ℝ) (o : Nat → ℝ) (m : Nat) :
    splitValue 64 (pairV b s o m) = (wordV b s o (2 * m), wordV b s o (2 * m + 1)) ∧
      (pairV b s o m).bytes = 8 ∧ (wordV b s o (2 * m)).bytes = 4 ∧
      (wordV b s o (2 * m + 1)).bytes = 4 := by
  cases b
  · simp [pairV, wordV, splitValue, Value.bytes, FloatFmt.bytes]
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

private def un (q : Nat) : YItem := .unpack 64 (1832 + 2 * q) (1833 + 2 * q) (2479 + q)

private def unOk (q : Nat) : Bool := match kernel.code[2750 + 3 * q]? with
  | some ⟨none, .move ⟨.unpack, .int .b 64, [some lo, some hi], [.reg a]⟩⟩ =>
    decide (lo = 1832 + 2 * q ∧ hi = 1833 + 2 * q ∧ a = 2479 + q)
  | _ => false

private theorem un_ok : ∀ q : Fin 32, unOk q.val = true := by decide +kernel

private theorem un_code (q : Fin 32) :
    kernel.code[2750 + 3 * q.val]? = some ⟨none, (un q.val).op⟩ := by
  have h := un_ok q
  unfold unOk at h
  split at h
  · rename_i hc
    simp only [decide_eq_true_eq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact hc
  · contradiction

private theorem un_emu : ∀ q : Fin 32,
    Assumptions.emuSites.contains (2750 + 3 * q.val) = false := by decide +kernel

/-- **The unpack at pc `2750 + 3 q`** puts the halves of the pair into its two registers. -/
theorem unpack_tau {b t : TState} {q : Nat} (hq : q < 32) (hpc : b.pc = 2750 + 3 * q) {v : Value}
    (hv : b.regs (2479 + q) = some v) (h8 : v.bytes = 8)
    (h4 : (splitValue 64 v).1.bytes = 4 ∧ (splitValue 64 v).2.bytes = 4)
    (h : Tau kernel Assumptions.all L g b t) :
    t.regs (1832 + 2 * q) = some (splitValue 64 v).1 ∧
      t.regs (1833 + 2 * q) = some (splitValue 64 v).2 ∧
      ∀ r, r ≠ 1832 + 2 * q → r ≠ 1833 + 2 * q → t.regs r = b.regs r := by
  have hc : kernel.code[b.pc]? = some ⟨none, (un q).op⟩ := by
    rw [hpc]; exact un_code ⟨q, hq⟩
  have hS := Kernels.InklingRelDecode.Proof.segFree (hpc ▸ un_emu ⟨q, hq⟩)
  have hR : (un q).Rule Assumptions.all L g b :=
    YItem.unpack_rule (pc := b.pc) rfl (fun s hs a' ha' =>
      moveNone (by omega) (by omega) (by omega) _ a' ha') b rfl
  have hx := (YItem.exec (un q) (V := fun r => (b.regs r).getD (.bits 32 0)) hS hR
    (fun r hr => by
      simp only [un, YItem.reads, List.mem_singleton] at hr
      subst hr
      simp [hv]) rfl).1 (by simpa [un, YItem.cond, hv] using ⟨h8, h4⟩)
  have hl : (un q).op.isLocal = true := rfl
  have hex : execLocalA Assumptions.all L g b (un q).op = .ok t := by
    unfold Tau out at h
    cases hf : b.fault with
    | some f => simp [hf] at h
    | none =>
      simp only [hf, hc, guardHolds, hl, pure, Except.pure, ↓reduceIte] at h
      cases hx' : execLocalA Assumptions.all L g b (un q).op with
      | error f => simp [hx'] at h
      | ok u =>
        simp only [hx', Out.tau.injEq] at h
        rw [h]
  rw [hex] at hx
  obtain rfl := (Except.ok.inj hx).symm
  refine ⟨?_, ?_, fun r h1 h2 => ?_⟩
  · simp [un, YItem.post, YItem.vals, setReg, PTX.next, hv, Function.update_of_ne]
  · simp [un, YItem.post, YItem.vals, setReg, PTX.next, hv]
  · simp [un, YItem.post, YItem.vals, setReg, PTX.next, Function.update_of_ne h1,
      Function.update_of_ne h2]

/-- A one-source weak store through a base register, which advances when it continues. -/
def stAdv (ins : Instr) : Bool := match ins.op with
  | .mem m => decide (m.rule = some .threadAccess ∧ m.kind = .store ∧ m.sem = .weak) &&
    m.locSpace?.isSome && (match m.addr.base with | .reg _ _ => true | _ => false) &&
    (match m.srcs with | [.reg _] => true | _ => false)
  | _ => false

theorem stAdv_adv {ins : Instr} (h : stAdv ins = true) {A : List Assumption} {t u : TState}
    {pc : Nat} {e : Event} (hf : Fires pc (eventTmpl A L g t ins.op) e (some u)) :
    u.pc = t.pc + 1 := by
  obtain ⟨gd, op⟩ := ins
  cases op <;> simp only [stAdv] at h <;> try contradiction
  rename_i m
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hr, hk, hsem⟩, hsp⟩, hb⟩, hsrc⟩ := h
  obtain ⟨sp, hsp'⟩ := Option.isSome_iff_exists.mp hsp
  rcases hbase : m.addr.base with ⟨⟩ | ⟨base, w⟩ <;> rw [hbase] at hb <;> try simp at hb
  rcases hs : m.srcs with _ | ⟨x, _ | ⟨y, ys⟩⟩ <;> rw [hs] at hsrc <;> try simp at hsrc
  cases x <;> try simp at hsrc
  rename_i src
  exact (fires_st_adv (a := m) hr hsp' hbase hk hsem hs hf).2.1

/-- **The event entry scan**: an event that lands at `P` is at a position of `preds`, or is an
advancing store at `P`. -/
def evLandS (P : Nat) (preds : List Nat) : Bool :=
  scanCode (fun pc ins => ins.op.isLocal ||
    ((pc + 1 != P || preds.contains pc) && (pc != P || stAdv ins))) kernel.code 0

/-- **A state of the lane at `P`** follows a local step or an event from a state at `preds`. -/
theorem back_one {P preds} (hpr : predOk P preds = true) (hev : evLandS P preds = true)
    (hP : P ≠ 0) {w : TState} (hl : Iface.LaneState L X g w) (hw : w.pc = P) :
    ∃ c, Iface.LaneState L X g c ∧ c.pc ∈ preds ∧
      (Tau kernel Assumptions.all L g c w ∨
        ∃ e, EStep kernel Assumptions.all L g c e (some w)) := by
  obtain ⟨k, t0, hr, hrt⟩ := hl
  obtain ⟨k0, hk0, hr0⟩ := run_norm hr
  rcases Relation.ReflTransGen.cases_tail hrt with rfl | ⟨c, hc, ht⟩
  · cases k0 with
    | zero =>
      rw [List.take_zero] at hr0
      cases hr0
      simp at hw
      omega
    | succ k =>
      obtain ⟨e, he'⟩ : ∃ e, (X.tr g)[k]? = some e :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨u, c, hu, hus, hes⟩ := pre_idx he' hr0
      obtain ⟨ins, hci, hnl, hf⟩ := EventFrame.estep_event_source hes
      have hp := post_pc hes
      have hsc := scanCode_get hev hci
      rw [Nat.zero_add] at hsc
      simp only [hnl, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at hsc
      refine ⟨c, ⟨k, u, hu, hus⟩, ?_, .inr ⟨e, hes⟩⟩
      obtain ⟨h1, h2⟩ := hsc
      rcases (by omega : c.pc = P ∨ c.pc + 1 = P) with h | h
      · rcases h2 with h2 | h2
        · exact absurd h h2
        · have := stAdv_adv h2 hf
          omega
      · rcases h1 with h1 | h1
        · exact absurd h h1
        · simpa using h1
  · exact ⟨c, ⟨k, t0, hr, hc⟩, pred_of_tau hpr ht hw, .inl ht⟩

private theorem pr1 : ∀ q : Fin 32, predOk (2751 + 3 * q.val) [2750 + 3 * q.val] = true := by
  decide +kernel

private theorem land1 : ∀ q : Fin 32,
    evLandS (2751 + 3 * q.val) [2750 + 3 * q.val] = true := by decide +kernel

private theorem pr2 : ∀ q : Fin 32, predOk (2752 + 3 * q.val) [2751 + 3 * q.val] = true := by
  decide +kernel

private theorem land2 : ∀ q : Fin 32,
    evLandS (2752 + 3 * q.val) [2751 + 3 * q.val] = true := by decide +kernel

private theorem keep1 : ∀ q : Fin 32, (match kernel.code[2751 + 3 * q.val]? with
    | some ins => !ins.op.isLocal && !(EventFrame.eventWrites ins.op).contains (1833 + 2 * q.val)
    | none => false) = true := by decide +kernel

variable {b : Bool} {sc : ℝ} {o : Nat → ℝ}

/-- **The registers of the first store's unpack**, at the state of the first store. -/
theorem word_first
    (hpair : ∀ t, Iface.LaneState L X g t → 2674 ≤ t.pc → t.pc ≤ 2846 → ∀ m < 32,
      t.regs (2479 + m) = some (pairV b sc o m))
    {q : Nat} (hq : q < 32) {s : TState} (hs : Iface.LaneState L X g s)
    (hpc : s.pc = 2751 + 3 * q) :
    s.regs (1832 + 2 * q) = some (wordV b sc o (2 * q)) ∧
      s.regs (1833 + 2 * q) = some (wordV b sc o (2 * q + 1)) := by
  obtain ⟨c, hc, hcp, hT⟩ := back_one (pr1 ⟨q, hq⟩) (land1 ⟨q, hq⟩) (by omega) hs hpc
  have hcpc : c.pc = 2750 + 3 * q := by simpa using hcp
  rcases hT with hT | ⟨e, hes⟩
  swap
  · exfalso
    obtain ⟨ins, hci, hnl, -⟩ := EventFrame.estep_event_source hes
    rw [hcpc, un_code ⟨q, hq⟩] at hci
    obtain rfl := (Option.some.inj hci).symm
    have hl : (un q).op.isLocal = true := rfl
    exact absurd (hl.symm.trans hnl) (by decide)
  obtain ⟨hsp, h8, h4a, h4b⟩ := split_pair b sc o q
  obtain ⟨r1, r2, -⟩ := unpack_tau hq hcpc (hpair c hc (by omega) (by omega) q hq) h8
    (by rw [hsp]; exact ⟨h4a, h4b⟩) hT
  rw [hsp] at r1 r2
  exact ⟨r1, r2⟩

/-- **The register of the second store's word**, at the state of the second store. -/
theorem word_second
    (hpair : ∀ t, Iface.LaneState L X g t → 2674 ≤ t.pc → t.pc ≤ 2846 → ∀ m < 32,
      t.regs (2479 + m) = some (pairV b sc o m))
    {q : Nat} (hq : q < 32) {s : TState} (hs : Iface.LaneState L X g s)
    (hpc : s.pc = 2752 + 3 * q) : s.regs (1833 + 2 * q) = some (wordV b sc o (2 * q + 1)) := by
  obtain ⟨c, hc, hcp, hT⟩ := back_one (pr2 ⟨q, hq⟩) (land2 ⟨q, hq⟩) (by omega) hs hpc
  have hcpc : c.pc = 2751 + 3 * q := by simpa using hcp
  have kp := keep1 ⟨q, hq⟩
  rw [← hcpc] at kp
  rcases hT with hT | ⟨e, hes⟩
  · obtain ⟨ins, hci, -, hk⟩ := win_cases hT
    rw [hci] at kp
    rcases hk with ⟨-, -, hreg⟩ | ⟨hl, -, -⟩
    · rw [hreg, (word_first hpair hq hc hcpc).2]
    · simp [hl] at kp
  · obtain ⟨ins, hci, -, -⟩ := EventFrame.estep_event_source hes
    rw [hci] at kp
    rw [Lib.estep_keeps hes ins hci _ (by simp at kp; exact kp.2)]
    exact (word_first hpair hq hc hcpc).2

private def stOk (j : Nat) : Bool := match kernel.code[2751 + j + j / 2]? with
  | some ⟨_, .mem m⟩ => decide (GlobalStore m (2380 + j) (1832 + j))
  | _ => false

private theorem st_ok : ∀ j : Fin 64, stOk j.val = true := by decide +kernel

private theorem wordV_bytes : (wordV b sc o j).bytes = 4 := by
  cases b <;> simp [wordV, Value.bytes, FloatFmt.bytes, b32]

/-- **An epilogue word store writes the bytes of its word.** -/
theorem store_word {m : Mem0} (hX : Consistent L kernel Assumptions.all m X)
    (hpair : ∀ t, Iface.LaneState L X g t → 2674 ≤ t.pc → t.pc ≤ 2846 → ∀ m < 32,
      t.regs (2479 + m) = some (pairV b sc o m))
    {k j : Nat} {a : Acc} {bs : List Byte} (hj : j < 64)
    (he : X.get (g, k) = some ⟨2751 + j + j / 2, .wr a bs⟩) :
    bs = (wordV b sc o j).toBytes := by
  obtain ⟨s, u, hs, hes⟩ := lane_of_event hX he (by simp [Ends])
  obtain ⟨ins, hci, -, hf⟩ := EventFrame.estep_event_source hes
  have hspc := EventFrame.estep_source_pc hes
  have hpc : s.pc = 2751 + j + j / 2 := by simpa using hspc.symm
  have hv : s.regs (1832 + j) = some (wordV b sc o j) := by
    obtain ⟨q, hq, rfl | rfl⟩ : ∃ q, q < 32 ∧ (j = 2 * q ∨ j = 2 * q + 1) :=
      ⟨j / 2, by omega, by omega⟩
    · exact (word_first hpair hq hs (by omega)).1
    · have := word_second hpair hq hs (by omega)
      rwa [show 1832 + (2 * q + 1) = 1833 + 2 * q by omega]
  have hk := st_ok ⟨j, hj⟩
  unfold stOk at hk
  rw [hpc] at hci
  rw [hci] at hk
  obtain ⟨gd, op⟩ := ins
  cases op <;> simp only [] at hk <;> try contradiction
  rename_i mm
  have hm := of_decide_eq_true hk
  obtain ⟨hr, hsp, hb, hkd, hsem, hw, -, hsrc⟩ := hm
  obtain ⟨hsub, -, -⟩ := fires_st_adv (hr) (sp := .global) (by simpa using hsp) hb hkd hsem hsrc hf
  obtain ⟨acc, hacc⟩ := fires_st_srcBytes hr (by simpa using hsp) hb hkd hsem hsrc
    (by rw [hw]; exact wordV_bytes) hsub hv hf (fun f h => by cases h)
  exact (Kind.wr.inj hacc).2

end
end PTX.Kernels.InklingRelDecode.Proof.Protocol.Values
