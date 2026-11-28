-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module
public import Kernels.InklingRelDecode.Proof.Softmax.Strict.RouteK
import Kernels.InklingRelDecode.Proof.Softmax.GenRulesO
import Kernels.InklingRelDecode.Proof.Softmax.Data.RescaleSteps
import Kernels.InklingRelDecode.Flow.Code.Part035
import Lemmas.Flow.TypedDeclH
import Lemmas.Flow.DataElems
@[expose] public section
/-! # The strict step of the wait for the accumulator load: the rescale run (pcs 2262 to 2325) -/
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Flow.Havoc PTX.Assumption
open PTX.Kernels.InklingRelDecode.Gen.TypedLateQt
set_option maxRecDepth 100000
variable {e : Control.Entry} {L : Launch} {g : Nat} {i : Nat} {v : Control.Carry} {w : Data.Vals}

/-- **A local instruction that writes a datum under the lane's fact**, the written word known. -/
theorem segQR_set {qt : Nat → EnvF} {R : TState → Prop} {pc d : Nat} {tg : TagF} {op : Op}
    {F G : List (Nat × Value)} {x : Value} (hc : kernel.code[pc]? = some ⟨none, op⟩)
    (hl : op.isLocal = true)
    (hex : ∀ t, At t pc F → TypedF (qt pc) t → R t →
      execLocalA Assumptions.all L g t op = .ok (PTX.next (setReg t d x)))
    (hv : ∀ t, At t pc F → TypedF (qt pc) t → R t → tg.ok (some x))
    (hq : afterF qt pc [(d, tg)] = true) (hG : ∀ p ∈ G, p = (d, x) ∨ (p ∈ F ∧ p.1 ≠ d)) :
    SegQ kernel Assumptions.all L g (fun t => QTF qt t ∧ TauAll kernel Assumptions.all L g R t)
      pc F (pc + 1) G := by
  intro t ht ⟨hQ, hT⟩
  obtain ⟨hpc, hsub, hacc, hflt, hregs⟩ := id ht
  have hty : TypedF (qt pc) t := by simpa [QTF, hpc] using hQ
  have hR := hT t .refl
  have htau := tau_of_ok (A := Assumptions.all) (L := L) (g := g) (by rw [hpc]; exact hc) hl
    hflt (hex t ht hty hR)
  obtain ⟨hw1, hw2⟩ := wr1 (t := t) (d := d) (tg := tg) (hv t ht hty hR)
  refine ⟨_, .single htau, ⟨by simp [PTX.next, setReg, hpc], hsub, hacc, hflt,
    holds_of_mem fun r y hm => ?_⟩,
    QTF.after1 hQ hpc (by simp [PTX.next, setReg, hpc]) hw1 hw2 hq,
    fun u hu => hT u (.head htau hu)⟩
  rcases hG _ hm with h | ⟨hp, hne⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    simp [PTX.next, setReg]
  · simp only [PTX.next, setReg]
    rw [Function.update_of_ne hne]
    exact holds_mem hregs hp

/-- The product of the rescale factor and the `k`-th loaded word. -/
noncomputable def rsP (V : Nat → Value) (k : Nat) : Value :=
  okVal (b32 0) (mulE false (V 507) (V (1547 + k)))

theorem rs_code : ∀ k < 64, OItem.instrB kernel.code[2262 + k]?
    (OItem.mul false (1612 + k) 507 (1547 + k)).op = true := by decide +kernel

theorem rs_tag_a : ∀ k < 64, d32 (lateQt (2262 + k)) 507 = true := by decide +kernel

theorem rs_tag_b : ∀ k < 64, d32 (lateQt (2262 + k)) (1547 + k) = true := by decide +kernel

theorem rs_tag_c : ∀ k < 64, afterF lateQt (2262 + k) [(1612 + k, TagF.dat32)] = true := by
  decide +kernel

theorem rs_tag_d : ∀ k < 64, Iface.declinePc (2262 + k) = true ∧
    Assumptions.emuSites.contains (2262 + k) = false := by decide +kernel

/-- **The product of the rescale at `2262 + k`** is the exact word, a datum. -/
theorem rs_exec (V : Nat → Value) (k : Nat) (hk : k < 64) {F : List (Nat × Value)}
    (h1 : (507, V 507) ∈ F) (h2 : (1547 + k, V (1547 + k)) ∈ F) {t : TState}
    (ht : At t (2262 + k) F) (hT : TypedF (lateQt (2262 + k)) t) (hR : LateR' L g t) :
    execLocalA Assumptions.all L g t (OItem.mul false (1612 + k) 507 (1547 + k)).op =
      .ok (PTX.next (setReg t (1612 + k) (rsP V k))) ∧ Dat32 (rsP V k) := by
  have t1 := rs_tag_a k hk
  have t2 := rs_tag_b k hk
  have t3 := rs_tag_c k hk
  obtain ⟨t4, t5⟩ := rs_tag_d k hk
  have hcode := OItem.instrB_eq (rs_code k hk)
  obtain ⟨hpc, -, -, -, hregs⟩ := ht
  have ra : t.regs 507 = some (V 507) := holds_mem hregs h1
  have rb : t.regs (1547 + k) = some (V (1547 + k)) := holds_mem hregs h2
  have da := dat32_regs ra hT t1
  have db := dat32_regs rb hT t2
  have hnd := hR.1.1 (hpc ▸ t4) _ (hpc ▸ hcode)
  have hrs : rsPc (2262 + k) = true := by simp only [rsPc, decide_eq_true_eq]; omega
  obtain ⟨hI, hD⟩ := rule_mulRs (L := L) (g := g) (fz := false) (d := 1612 + k) (a := 507)
    (b := 1547 + k) (2262 + k) hrs t hpc
  obtain ⟨y, hy, hdy⟩ := mulD_step' hI (OpndIs.reg ra) (OpndIs.reg rb) da db hnd
  have hy' : execLocalA Assumptions.all L g t (OItem.mul false (1612 + k) 507 (1547 + k)).op =
      .ok (PTX.next (setReg t (1612 + k) y)) := hy
  have hr : ∀ r ∈ (XItem.base (OItem.mul false (1612 + k) 507 (1547 + k))).reads,
      t.regs r = some (V r) := by
    intro r hr
    simp only [XItem.reads, OItem.reads, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ra
    · exact rb
  have hx := XItem.exec (XItem.base (OItem.mul false (1612 + k) 507 (1547 + k))) (V := V)
    (t := t) (hpc ▸ segFree t5) ⟨hI, hD⟩ hr rfl
  by_cases hc : (XItem.base (OItem.mul false (1612 + k) 507 (1547 + k))).cond V
  · have h2' : execLocalA Assumptions.all L g t (OItem.mul false (1612 + k) 507 (1547 + k)).op =
        .ok (XItem.post V (XItem.base (OItem.mul false (1612 + k) 507 (1547 + k))) t) := hx.1 hc
    have hpost : XItem.post V (XItem.base (OItem.mul false (1612 + k) 507 (1547 + k))) t =
        PTX.next (setReg t (1612 + k) (rsP V k)) := by
      simp [XItem.post, XItem.vals, OItem.vals, rsP]
      rfl
    rw [hpost, hy'] at h2'
    have hyy := congrArg (fun s => s.regs (1612 + k)) (Except.ok.inj h2')
    simp [PTX.next, setReg] at hyy
    subst hyy
    exact ⟨hy', hdy⟩
  · obtain ⟨f, hf⟩ := hx.2 hc
    have hf' : execLocalA Assumptions.all L g t (OItem.mul false (1612 + k) 507
        (1547 + k)).op = .error f := hf
    rw [hy'] at hf'
    cases hf'

/-- **One of the 64 products of the rescale** is exact. -/
theorem rs_step (V : Nat → Value) (k : Nat) (hk : k < 64) {F G : List (Nat × Value)}
    (h1 : (507, V 507) ∈ F) (h2 : (1547 + k, V (1547 + k)) ∈ F)
    (hG : ∀ p ∈ G, p = (1612 + k, rsP V k) ∨ (p ∈ F ∧ p.1 ≠ 1612 + k)) :
    SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) (2262 + k) F
      (2262 + k + 1) G := by
  have t1 := rs_tag_a k hk
  have t2 := rs_tag_b k hk
  have t3 := rs_tag_c k hk
  obtain ⟨t4, t5⟩ := rs_tag_d k hk
  exact segQR_set (d := 1612 + k) (tg := .dat32) (x := rsP V k)
    (OItem.instrB_eq (rs_code k hk)) rfl
    (fun t ht hT hR => (rs_exec V k hk h1 h2 ht hT hR).1)
    (fun t ht hT hR => ⟨_, rfl, (rs_exec V k hk h1 h2 ht hT hR).2⟩) t3 hG

/-- The products so far. -/
noncomputable def rsPs (V : Nat → Value) (n : Nat) : List (Nat × Value) :=
  (List.range n).map fun j => (1612 + j, rsP V j)

theorem rs_facts2_eq (V : Nat → Value) : Gen.rs_facts2 V =
    [(168, V 168), (498, V 498), (507, V 507), (1522, V 1522)] ++ rsPs V 64 ++
      [(1914, V 1914)] := by
  rfl

theorem rs_all (V : Nat → Value) {B : List (Nat × Value)} (h1 : (507, V 507) ∈ B)
    (h2 : ∀ k < 64, (1547 + k, V (1547 + k)) ∈ B) (h3 : ∀ p ∈ B, ∀ k < 64, p.1 ≠ 1612 + k) :
    ∀ n ≤ 64, SegQ kernel Assumptions.all L g (LQ Assumptions.all L g (LateR' L g)) 2262 B
      (2262 + n) (rsPs V n ++ B) := by
  intro n
  induction n with
  | zero => exact fun _ => SegQ.weaken fun _ h => by simpa [rsPs] using h
  | succ n ih =>
    intro hn
    refine (ih (by omega)).comp (rs_step V n (by omega) (List.mem_append_right _ h1)
      (List.mem_append_right _ (h2 n (by omega))) ?_)
    intro p hp
    rcases List.mem_append.mp hp with h | h
    · simp only [rsPs, List.range_succ, List.map_append, List.mem_append, List.map_cons,
        List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h
      · refine .inr ⟨List.mem_append_left _ h, ?_⟩
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
        have := List.mem_range.mp hj
        simp
        omega
      · exact .inl h
    · exact .inr ⟨List.mem_append_right _ h, h3 p h n (by omega)⟩

theorem rs0_eq (V : Nat → Value) : Gen.rs_facts0 V = ([168, 498, 507, 1522] ++
    (List.range 64).map (1547 + ·) ++ [1914]).map (fun r => (r, V r)) := rfl

theorem rs0_mem (V : Nat → Value) {r : Nat} (h1 : 1547 ≤ r) (h2 : r < 1611) :
    (r, V r) ∈ Gen.rs_facts0 V := by
  rw [rs0_eq]
  exact List.mem_map.mpr ⟨r, List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.mpr ⟨r - 1547, List.mem_range.mpr (by omega), by omega⟩)), rfl⟩

/-- **The wait for the accumulator load** continues at the barrier after the rescale. -/
theorem sstep_waitLdO (ev : Event) :
    (Data.code e L g).StepForQP (QTF lateQt) (TauAll kernel Assumptions.all L g (LateR' L g))
      LWf ⟨⟨.waitLdO, i, v⟩, w⟩ ev := by
  refine adv_soft (d := ⟨⟨.waitLdO, i, v⟩, w⟩) (dn := ⟨⟨.bar24, i, v⟩, w⟩) (p := 2261) rfl
    Flow.code_2261 (fun _ => Code.fires_tcWaitLd_next)
    (fun ev => by obtain ⟨_, k⟩ := ev; cases k <;> rfl)
    (fun hi => Control.body_inv hi rfl rfl) (by decide +kernel) (by decide +kernel) ?_ ev
  change SegQ kernel Assumptions.all L g _ 2262 (Gen.rs_facts0 (Data.rsV L w) ++ _) 2326
    (Gen.rs_facts2 (Data.rsV L w) ++ _)
  rw [rs_facts2_eq]
  refine (rs_all (Data.rsV L w) (B := Gen.rs_facts0 (Data.rsV L w) ++ factsFrom
    (Control.ctlLive 2262) (Control.valueOf e L g ⟨.waitLdO, i, v⟩))
    (List.mem_append_left _ (by simp [Gen.rs_facts0]))
    (fun k hk => List.mem_append_left _ (rs0_mem _ (by omega) (by omega))) ?_ 64 le_rfl).comp
    (SegQ.weaken fun _ hR => holds_of_forall fun p hp => ?_)
  · intro p hp k hk
    rcases List.mem_append.mp hp with h | h
    · have : p.1 ∈ Data.dKeys .waitLdO := by
        rw [← Data.dFS_keys L .waitLdO w]
        exact List.mem_map_of_mem h
      exact (by decide +kernel : ∀ k < 64, ∀ r ∈ Data.dKeys .waitLdO, r ≠ 1612 + k) k hk _ this
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
      exact (by decide +kernel : ∀ k < 64, ∀ r ∈ Control.ctlLive 2262, r ≠ 1612 + k) k hk r hr
  · refine holds_mem hR ?_
    rcases List.mem_append.mp hp with h | h
    · have key : p ∈ rsPs (Data.rsV L w) 64 ∨ p ∈ Gen.rs_facts0 (Data.rsV L w) := by
        rcases List.mem_append.mp h with h | h
        · rcases List.mem_append.mp h with h | h
          · right
            simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with rfl | rfl | rfl | rfl <;> simp [Gen.rs_facts0]
          · exact .inl h
        · right
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl
          simp [Gen.rs_facts0]
      rcases key with h' | h'
      · exact List.mem_append_left _ h'
      · exact List.mem_append_right _ (List.mem_append_left _ h')
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
      exact List.mem_append_right _ (List.mem_append_right _ (mem_factsFrom
        ((by decide +kernel : ∀ r ∈ Control.ctlLive 2326, r ∈ Control.ctlLive 2262) r hr)))
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Strict
