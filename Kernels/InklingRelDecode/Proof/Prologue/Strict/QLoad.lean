-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.QStore

@[expose] public section

/-! # The strict query loads

The step of a load whose group is on: the register takes the half, the move after it makes
the zero half of the next register, and the loads of the groups that are off are skipped. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Control Arith32

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

/-- The halves after the load `j` returned `x`. -/
def upd (v : Data.Vals) (j : Fin 64) (x : Value) : Data.Vals :=
  ⟨v.pay, Function.update v.q j x⟩

theorem ldq_lt : ∀ j k : Fin 64, Data.Tag.qh k ∈ Data.tags (.ldq j) → k.val < j.val := by
  decide +kernel

theorem ldq_no_qw : ∀ (j : Fin 64) (i : Fin 8) (k : Fin 4), Data.Tag.qw i k ∉ Data.tags (.ldq j)
    := by
  decide +kernel

theorem tag_val_upd (c : Control.D) (v : Data.Vals) (x : Value) (j : Fin 64) (s s' : Site)
    (τ : Data.Tag) (h : τ ∈ Data.tags (.ldq j)) :
    τ.val Q L g (dq c (upd v j x) s') = τ.val Q L g (dq c v s) := by
  cases τ with
  | qh k =>
    have hk := ldq_lt j k h
    simp only [Data.Tag.val, Data.qv, upd, dq, Function.update_of_ne (Fin.ne_of_lt hk)]
    rfl
  | qw i k => exact absurd h (ldq_no_qw j i k)
  | _ => rfl

/-- The facts of the state after load `j` are among those before it and the load's. -/
theorem mem_upd (c : Control.D) (v : Data.Vals) (x : Value) (j : Fin 64)
    (hon : queryOn (g % L.block) (j.val / 16) c = true) (s' : Site)
    (ht : ∀ τ ∈ Data.tags s', τ ∈ Data.tags (.ldq j) ∨ τ = .qh j)
    (hl : (ctlLive s'.pc).isSublist (ctlLive (queryPc j)) = true) :
    ∀ q ∈ dFacts Q L g w (dq c (upd v j x) s'),
      q ∈ (qDst j, x) :: dFacts Q L g w (dq c v (.ldq j)) := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp hq
    rcases ht τ hτ with h | rfl
    · rw [tag_val_upd (Q := Q) (L := L) (g := g) c v x j (.ldq j) s' τ h]
      exact List.mem_cons_of_mem _ (mem_tag (w := w) (d := dq c v (.ldq j)) h)
    · have : Data.Tag.val Q L g (dq c (upd v j x) s') (.qh j) = x := by
        have h0 : queryOn (g % L.block) (j.val / 16) (dq c (upd v j x) s').c = true := hon
        simp [Data.Tag.val, Data.qv, h0, upd, dq]
      rw [this]
      exact List.mem_cons_self
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    exact List.mem_cons_of_mem _ (mem_ctl (w := w) (d := dq c v (.ldq j))
      ((List.isSublist_iff_sublist.mp hl).subset hr))


/-- The last load, skipped, passes to the first store. -/
theorem qs_to_stq (c : Control.D) (v : Data.Vals) (a : Fin 64) (hv : ∀ k, (v.q k).bytes = 2)
    (hoff : ∀ k, a.val ≤ k → k < 64 → queryOn (g % L.block) (k / 16) c = false) :
    SegQ kernel Assumptions.all L g (QT proQt) (queryPc a) (SkipF Q L g w c v a) 526
      (dFacts Q L g w (dq c v (.stq 0 0))) := by
  have run := qs_run (Q := Q) (L := L) (g := g) (w := w) c v (63 - a.val) a.val 63 (by omega)
    (fun k hk hk' => hoff k hk (by omega))
  have h63 : queryOn (g % L.block) (63 / 16) c = false := hoff 63 (by omega) (by omega)
  refine SegQ.comp (b := queryPc 63) (G := SkipF Q L g w c v 63) (by simpa using run)
    (SegQ.comp (b := 515) (G := SkipF Q L g w c v 63)
    (SegQ.skipG (pick := false) (neg := false) (p := queryPred 63)
      (qLoadPair (L := L) (g := g) 63).2 (fun R hR => ?_) rfl (fun _ h => h)
      (by decide +kernel)) (to_stq0 c v Data.zeroV hv ?_))
  · have := holds_mem hR (List.mem_cons_of_mem _ (mem_ctl (w := w)
      (d := dq c v (.ldq 63)) (query_live 63)))
    rw [query_value] at this
    have h0 : queryOn (g % L.block) (63 / 16) (dq c v (.ldq 63)).c = false := h63
    simpa [h0] using this
  · have h0 : queryOn (g % L.block) (63 / 16) (dq c v (.ldq 63)).c = false := h63
    simp [Data.qv, h0]
    rfl


theorem upd_bytes (v : Data.Vals) (j : Fin 64) (x : Value) (hv : ∀ k, (v.q k).bytes = 2)
    (bx : x.bytes = 2) (k : Fin 64) : ((upd v j x).q k).bytes = 2 := by
  by_cases h : k = j
  · subst h; simpa [upd] using bx
  · simpa [upd, Function.update_of_ne h] using hv k

/-- **The move after a load** and the weakening to the next load's skipped facts. -/
theorem ld_move (c : Control.D) (v : Data.Vals) (x : Value) (j : Fin 63)
    (hon : queryOn (g % L.block) (j.val / 16) c = true) :
    SegQ kernel Assumptions.all L g (QT proQt) (queryPc (f64 j) + 1)
      ((qDst (f64 j), x) :: dFacts Q L g w (dq c v (.ldq (f64 j)))) (queryPc (f64s j))
      (SkipF Q L g w c (upd v (f64 j) x) (f64s j)) := by
  obtain ⟨hk1, hk2, hk3⟩ := q_fresh j
  obtain ⟨hlo, hhi⟩ := q_move_pc j
  have hz : (199, Data.zeroV) ∈ (qDst (f64 j), x) :: dFacts Q L g w (dq c v (.ldq (f64 j))) :=
    List.mem_cons_of_mem _ (mem_tag (w := w) (d := dq c v (.ldq (f64 j))) (τ := .zero) (by
      simp [Data.tags, Data.oldTags, Data.qTags]))
  have hn : qDst (f64s j) ∉ ((qDst (f64 j), x) ::
      dFacts Q L g w (dq c v (.ldq (f64 j)))).map Prod.fst := by
    simp only [List.map_cons, List.mem_cons, not_or]
    exact ⟨hk3, keys_notin (w := w) (d := dq c v (.ldq (f64 j))) hk1 hk2⟩
  have mv := move_seg (L := L) (g := g) (v := Data.zeroV) (OItem.instrB_eq (q_move_code j)) rfl rfl
    hlo hhi (fun t hF => hex_mov16 hz rfl t hF) (fun R hR => holds_update_cons hR hn)
    (q_move_tags j)
  rw [show queryPc (f64 j) + 1 + 1 = queryPc (f64s j) by rw [pc_succ]] at mv
  refine SegQ.comp mv (SegQ.sub fun q hq => ?_)
  rcases List.mem_cons.mp hq with rfl | hq
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (mem_upd (w := w) c v x (f64 j) hon (.ldq (f64s j)) (q_tags j)
      (by have := q_live j; rwa [← pc_succ] at this) q hq)

/-- **After a load**: the skipped loads of the groups that are off, to the next load. -/
theorem ldq_span (c : Control.D) (v : Data.Vals) (x : Value) (j : Fin 63)
    (hon : queryOn (g % L.block) (j.val / 16) c = true) (hi : Fin 64) (hji : j.val < hi.val)
    (hoff : ∀ n, j.val < n → n < hi.val → queryOn (g % L.block) (n / 16) c = false) :
    SegQ kernel Assumptions.all L g (QT proQt) (queryPc (f64 j) + 1)
      ((qDst (f64 j), x) :: dFacts Q L g w (dq c v (.ldq (f64 j)))) (queryPc hi)
      (dFacts Q L g w (dq c (upd v (f64 j) x) (.ldq hi))) := by
  refine SegQ.comp (ld_move (w := w) c v x j hon) (SegQ.comp (b := queryPc hi)
    (G := SkipF Q L g w c (upd v (f64 j) x) hi) ?_ (SegQ.sub fun q hq => List.mem_cons_of_mem _ hq))
  exact qs_run (w := w) c (upd v (f64 j) x) (hi.val - (j.val + 1)) (j.val + 1) hi (by omega)
    fun k hk hk' => hoff k (by omega) hk'

/-- **After a load, to the first store**: every later group is off. -/
theorem ldq_stq (c : Control.D) (v : Data.Vals) (x : Value) (j : Fin 63)
    (hon : queryOn (g % L.block) (j.val / 16) c = true) (hv : ∀ k, (v.q k).bytes = 2)
    (bx : x.bytes = 2)
    (hoff : ∀ n, j.val < n → n < 64 → queryOn (g % L.block) (n / 16) c = false) :
    SegQ kernel Assumptions.all L g (QT proQt) (queryPc (f64 j) + 1)
      ((qDst (f64 j), x) :: dFacts Q L g w (dq c v (.ldq (f64 j)))) 526
      (dFacts Q L g w (dq c (upd v (f64 j) x) (.stq 0 0))) :=
  SegQ.comp (ld_move (w := w) c v x j hon) (qs_to_stq (w := w) c (upd v (f64 j) x) (f64s j)
    (upd_bytes v _ x hv bx) fun k hk hk' => hoff k (lt_of_lt_of_le (Nat.lt_succ_self _) hk) hk')

/-- **After the last load** the first store. -/
theorem ldq_last (c : Control.D) (v : Data.Vals) (x : Value)
    (hon : queryOn (g % L.block) (63 / 16) c = true) (hv : ∀ k, (v.q k).bytes = 2)
    (bx : x.bytes = 2) :
    SegQ kernel Assumptions.all L g (QT proQt) 515
      ((qDst 63, x) :: dFacts Q L g w (dq c v (.ldq 63))) 526
      (dFacts Q L g w (dq c (upd v 63 x) (.stq 0 0))) := by
  refine SegQ.comp (b := 515) (G := (qDst 63, x) :: dFacts Q L g w (dq c (upd v 63 x) (.ldq 63)))
    (SegQ.sub fun q hq => ?_) (to_stq0 c (upd v 63 x) x ?_ ?_)
  · rcases List.mem_cons.mp hq with rfl | hq
    · exact List.mem_cons_self
    · exact mem_upd (w := w) c v x 63 hon (.ldq 63) (fun τ hτ => Or.inl hτ) (by decide +kernel) q hq
  · exact upd_bytes v 63 x hv bx
  · have h0 : queryOn (g % L.block) (63 / 16) (dq c (upd v 63 x) (.ldq 63)).c = true := hon
    simp [Data.qv, h0, upd, dq]

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
