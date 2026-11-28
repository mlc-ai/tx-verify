-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.WordsGoal
public import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Inp
public import Kernels.InklingRelDecode.Proof.Lib.WinSet
public import Lemmas.Flow.TypedHalfG

@[expose] public section

/-! # The types of the bias words along their paths

The table of the bias words (`WordsTab`) at the level of types: at every position of a path the
registers it lists hold a half (a word of two halves for the packs). The local steps keep this
without the table's values, so it holds at every state a lane reaches from the state after an
event that has it, not only at the first stop. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code PTX.Flow.TyG PTX.Kernels.InklingRelDecode.Proof.Lib

set_option maxRecDepth 100000
noncomputable section
variable {L : Launch} {g : Nat}

/-- What register `r` of the table holds: a word for a pack, a half for the others. -/
def TyK (r : Nat) (v : Value) : Prop := if 1916 ≤ r ∧ r < 1948 then Word32 v else Half16 v

/-- The registers the table lists at the position of `t` are defined and typed. -/
def TyAt (k : WK) (t : TState) : Prop := ∀ r ∈ wKeys k t.pc, ∃ v, t.regs r = some v ∧ TyK r v

/-- A state of the path's region (or at an event) with the typed registers. -/
def TyGood (k : WK) (t : TState) : Prop :=
  (inIvs (wIvs k) t.pc || evAtB kernel t.pc) = true ∧ TyAt k t

theorem word32_join {x y : Value} (hx : Half16 x) (hy : Half16 y) : Word32 (joinValue x y) := by
  rcases hx with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;> rcases hy with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · exact .inl ⟨_, rfl⟩
  · exact .inr ⟨_, _, rfl, .inl ⟨_, rfl⟩, .inr ⟨_, rfl⟩⟩
  · exact .inr ⟨_, _, rfl, .inr ⟨_, rfl⟩, .inl ⟨_, rfl⟩⟩
  · exact .inr ⟨_, _, rfl, .inr ⟨_, rfl⟩, .inr ⟨_, rfl⟩⟩

theorem bw_half {x : Value} (h : Bw x) : Half16 x := by
  rcases h with ⟨r, rfl⟩ | rfl
  · exact .inr ⟨r, rfl⟩
  · exact .inl ⟨0, rfl⟩

theorem tyk_half {r : Nat} {v : Value} (hr : ¬(1916 ≤ r ∧ r < 1948)) (h : Half16 v) :
    TyK r v := by
  simpa [TyK, hr] using h

/-- The pack of two bias words is a word of two halves. -/
theorem packV_word32 {x y : Value} (hx : Bw x) (hy : Bw y) : Word32 (packV x y) := by
  have e : packV x y = joinValue x y := by
    simp [packV, pack32E, bw_bytes hx, bw_bytes hy, okVal]
  rw [e]
  exact word32_join (bw_half hx) (bw_half hy)

/-- **A skipped guard or a local step from a position without a move keeps the types.** -/
theorem ty_plain {k : WK} {t t1 : TState} (hp : inIvs (wIvs k) t.pc = true)
    (hs : wSpec t.pc = none) (hT : TyAt k t) (h : Tau kernel Assumptions.all L g t t1) :
    TyGood k t1 := by
  obtain ⟨ins, hc, hat⟩ := tabScan_at (wtab_scan k) hp
  simp only [tabAt, wSpecB, hs, Option.isSome_none, Bool.false_or] at hat
  have hem : Assumptions.emuSites.contains t.pc = false := by
    have : t.pc ∈ pcsOf (wIvs k) := List.contains_iff_mem.mp (by rw [pcsOf_contains]; exact hp)
    simpa using List.all_eq_true.mp (wtab_emu k) t.pc this
  obtain ⟨ins', hc', -, hk⟩ := win_cases h
  have e : ins' = ins := Option.some.inj (hc'.symm.trans hc)
  rw [e] at hk
  have skip : (inIvs (wIvs k) (t.pc + 1) || evAtB kernel (t.pc + 1)) = true ∧
      ∀ r ∈ wKeys k (t.pc + 1), r ∈ wKeys k t.pc := by
    by_cases hl : ins.op.isLocal = true
    · simp only [hl, ↓reduceIte, Bool.and_eq_true, List.all_eq_true, List.mem_cons,
        List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hat
      obtain ⟨-, -, ⟨hq, hk⟩, -⟩ := hat
      exact ⟨hq, fun r hr => List.contains_iff_mem.mp (hk r hr).1⟩
    · simp only [hl, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, List.all_eq_true,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hat
      obtain ⟨-, ⟨hq, hk⟩, -⟩ := hat
      exact ⟨hq, fun r hr => List.contains_iff_mem.mp (hk r hr)⟩
  rcases hk with ⟨-, hpc, hr⟩ | ⟨hl, hpc, hr⟩
  · refine ⟨by rw [hpc]; exact skip.1, fun r hr' => ?_⟩
    rw [hpc] at hr'
    obtain ⟨v, hv, ht⟩ := hT r (skip.2 r hr')
    exact ⟨v, by rw [hr, hv], ht⟩
  · simp only [hl, ↓reduceIte, Bool.and_eq_true, List.all_eq_true, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hat
    obtain ⟨hbr, ⟨hq1, -⟩, hq2, -⟩ := hat
    have hpc' : t1.pc = nextPc ins.op t.pc ∨ t1.pc = t.pc + 1 := by
      cases hop : ins.op <;> simp_all [Lib.succs, nextPc, noBrx]
    have go : ∀ q, t1.pc = q → ((inIvs (wIvs k) q || evAtB kernel q) = true ∧
        ∀ r ∈ wKeys k q, (wKeys k t.pc).contains r = true ∧
          (!(writesRegs ins.op).contains r) = true) → TyGood k t1 := by
      intro q hq ⟨hin, hk⟩
      refine ⟨by rw [hq]; exact hin, fun r hr' => ?_⟩
      rw [hq] at hr'
      obtain ⟨hr1, hr2⟩ := hk r hr'
      obtain ⟨v, hv, ht⟩ := hT r (List.contains_iff_mem.mp hr1)
      have hnw : r ∉ writesRegs ins.op := fun h => by simp [h] at hr2
      exact ⟨v, by rw [hr r hnw (fun h => by rw [hem] at h; cases h), hv], ht⟩
    rcases hpc' with h1 | h1
    · exact go _ h1 hq1
    · exact go _ h1 hq2

/-- **A local step of a move item** writes its outcome. -/
theorem item_tau {pc d : Nat} {srcs : List Nat} {f : List Value → Exec Value} {op : Op}
    {t t1 : TState} (hc : kernel.code[pc]? = some ⟨none, op⟩) (hl : op.isLocal = true)
    (hpc : t.pc = pc) (hR : (XItem.fn op d srcs f).Rule Assumptions.all L g t)
    {W : Nat → Value} (hW : ∀ r ∈ srcs, t.regs r = some (W r))
    (h : Tau kernel Assumptions.all L g t t1) :
    ∃ v, f (srcs.map W) = .ok v ∧ t1 = PTX.next (setReg t d v) := by
  have hx := hR W hW
  unfold Tau out at h
  cases hf : t.fault with
  | some f => simp [hf] at h
  | none =>
    simp only [hf, hpc, hc, guardHolds, hl, hx, pure, Except.pure] at h
    cases hv : f (srcs.map W) with
    | error e => simp [hv, Except.map] at h
    | ok v =>
      simp only [hv, Except.map, ↓reduceIte, Out.tau.injEq] at h
      exact ⟨v, rfl, h.symm⟩

/-- The source registers of a move are no packs. -/
theorem wSpec_reads {pc : Nat} {sp : WSp} (h : wSpec pc = some sp) :
    ∀ r ∈ sp.item.reads, ¬(1916 ≤ r ∧ r < 1948) := by
  intro r hr
  unfold wSpec at h
  split_ifs at h
  all_goals
    obtain rfl := Option.some.inj h
    simp [WSp.item, XItem.reads, nxtReg] at hr
    try split_ifs at hr
    all_goals omega

/-- The destination of a move is a pack exactly for the packs. -/
theorem wSpec_dst {pc : Nat} {sp : WSp} (h : wSpec pc = some sp) {d : Nat}
    (hd : sp.item.writes = [d]) : (1916 ≤ d ∧ d < 1948) ↔ ∃ a b, sp = .pk d a b := by
  unfold wSpec at h
  split_ifs at h
  all_goals
    obtain rfl := Option.some.inj h
    simp [WSp.item, XItem.writes, nxtReg] at hd
    subst hd
    simp [nxtReg]
    try split_ifs
    all_goals omega

/-- **A move item keeps the types**: the table's registers at the next position are the item's
destination, typed by its outcome, or were there. -/
theorem ty_fn {k : WK} {t t1 : TState} {op : Op} {d : Nat} {srcs : List Nat}
    {f : List Value → Exec Value} (hc : kernel.code[t.pc]? = some ⟨none, op⟩)
    (hl : op.isLocal = true) (hR : (XItem.fn op d srcs f).Rule Assumptions.all L g t)
    (hrd : ∀ r ∈ srcs, r ∈ wKeys k t.pc)
    (hcov : ∀ r ∈ wKeys k (t.pc + 1), r = d ∨ r ∈ wKeys k t.pc)
    (hin : (inIvs (wIvs k) (t.pc + 1) || evAtB kernel (t.pc + 1)) = true)
    (hout : ∀ (W : Nat → Value) v, (∀ r ∈ srcs, TyK r (W r)) → f (srcs.map W) = .ok v → TyK d v)
    (hT : TyAt k t) (h : Tau kernel Assumptions.all L g t t1) : TyGood k t1 := by
  have hty : ∀ r ∈ srcs, ∃ v, t.regs r = some v ∧ TyK r v := fun r hr => hT r (hrd r hr)
  have hW : ∀ r ∈ srcs, t.regs r = some ((fun r => (t.regs r).getD dflt) r) := fun r hr => by
    obtain ⟨v, hv, -⟩ := hty r hr
    simp [hv]
  obtain ⟨v, hv, rfl⟩ := item_tau hc hl rfl hR hW h
  have hvt : TyK d v := hout _ v (fun r hr => by
    obtain ⟨w, hw, ht⟩ := hty r hr
    simpa [hw] using ht) hv
  refine ⟨by simpa [next, setReg] using hin, fun r hr => ?_⟩
  simp only [next, setReg] at hr ⊢
  rcases hcov r hr with rfl | hk
  · exact ⟨v, by simp, hvt⟩
  · obtain ⟨w, hw, ht⟩ := hT r hk
    by_cases hd : r = d
    · subst hd; exact ⟨v, by simp, hvt⟩
    · exact ⟨w, by simp [Function.update_of_ne hd, hw], ht⟩

/-- **A move of the path keeps the types.** -/
theorem ty_move {k : WK} {t t1 : TState} {sp : WSp} (hp : inIvs (wIvs k) t.pc = true)
    (hs : wSpec t.pc = some sp) (hT : TyAt k t) (h : Tau kernel Assumptions.all L g t t1) :
    TyGood k t1 := by
  obtain ⟨hc0, hk0⟩ := wok_of k hs
  simp only [wOkC, hs, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc0
  simp only [wOk, hs, hp, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true] at hk0
  obtain ⟨⟨hint, hcode⟩, -⟩ := hc0
  obtain ⟨⟨⟨hrd, hcov⟩, hin⟩, -⟩ := hk0
  have hc := OItem.instrB_eq hcode
  have hR := wItem_rule (L := L) (g := g) sp hint t rfl
  have hrd' : ∀ r ∈ sp.item.reads, r ∈ wKeys k t.pc := fun r hr =>
    List.contains_iff_mem.mp (List.all_eq_true.mp hrd r hr)
  have hcov' : ∀ r ∈ wKeys k (t.pc + 1), r ∈ sp.item.writes ∨ r ∈ wKeys k t.pc := fun r hr => by
    have := List.all_eq_true.mp hcov r hr
    simpa using this
  have hrp := wSpec_reads hs
  have hcv : ∀ {d : Nat}, sp.item.writes = [d] → ∀ r ∈ wKeys k (t.pc + 1),
      r = d ∨ r ∈ wKeys k t.pc := fun {d} hw r hr => by
    simpa [hw] using hcov' r hr
  cases sp with
  | mv d s =>
    have hd : ¬(1916 ≤ d ∧ d < 1948) := fun hh => by
      obtain ⟨a, b, e⟩ := (wSpec_dst hs (d := d) rfl).mp hh
      cases e
    have hsn := hrp s (by simp [WSp.item, XItem.reads])
    refine ty_fn hc rfl hR hrd' (hcv rfl) (by simpa using hin) (fun W v hW he => ?_) hT h
    have h1 := hW s (by simp)
    simp only [TyK, hd, hsn, ↓reduceIte] at h1 ⊢
    simp only [mv16E, List.map_cons, List.map_nil] at he
    split_ifs at he
    exact (Except.ok.inj he) ▸ h1
  | mi d =>
    have hd : ¬(1916 ≤ d ∧ d < 1948) := fun hh => by
      obtain ⟨a, b, e⟩ := (wSpec_dst hs (d := d) rfl).mp hh
      cases e
    refine ty_fn hc rfl hR hrd' (hcv rfl) (by simpa using hin) (fun W v hW he => ?_) hT h
    have he' : Except.ok dflt = Except.ok v := he
    obtain rfl := Except.ok.inj he'
    simp only [TyK, hd, ↓reduceIte]
    exact .inl ⟨0, rfl⟩
  | pk d a b =>
    have hd : 1916 ≤ d ∧ d < 1948 := (wSpec_dst hs (d := d) rfl).mpr ⟨a, b, rfl⟩
    have hna := hrp a (by simp [WSp.item, XItem.reads])
    have hnb := hrp b (by simp [WSp.item, XItem.reads])
    refine ty_fn hc rfl hR hrd' (hcv rfl) (by simpa using hin) (fun W v hW he => ?_) hT h
    have h1 := hW a (by simp)
    have h2 := hW b (by simp)
    simp only [TyK, hna, hnb, ↓reduceIte] at h1 h2
    simp only [TyK, hd, and_self, ↓reduceIte]
    simp only [pack32E, List.map_cons, List.map_nil] at he
    split_ifs at he
    obtain rfl := Except.ok.inj he
    exact word32_join h1 h2

/-- **A local step keeps the types of the table's registers.** -/
theorem ty_step {k : WK} {t t1 : TState} (hg : TyGood k t)
    (h : Tau kernel Assumptions.all L g t t1) : TyGood k t1 := by
  obtain ⟨hin, hT⟩ := hg
  rcases Bool.or_eq_true_iff.mp hin with hp | he
  · cases hs : wSpec t.pc with
    | none => exact ty_plain hp hs hT h
    | some sp => exact ty_move hp hs hT h
  · exact absurd h (no_tau_evAt he)

/-- **Every state the local steps reach from a typed state is typed.** -/
theorem ty_reach {k : WK} {u t : TState} (hu : TyGood k u)
    (h : Relation.ReflTransGen (Tau kernel Assumptions.all L g) u t) : TyGood k t := by
  induction h with
  | refl => exact hu
  | tail _ ht ih => exact ty_step ih ht

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
