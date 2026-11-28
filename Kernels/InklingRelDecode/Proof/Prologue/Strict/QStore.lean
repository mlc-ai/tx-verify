-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Strict.QSkip
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.QueryAddr
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.Store

@[expose] public section

/-! # The strict packs and addresses of the query stores -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged Control Arith32

set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {g : Nat} {w : Value}

theorem pack_code : ∀ (i : Fin 8) (k : Fin 4), OItem.instrB kernel.code[522 + 6 * i.val + k.val]?
    (.move ⟨.pack, .int .b 32, [some (747 + 5 * i.val + k.val)],
      [.reg (qDst (Data.pk i k 0)), .reg (qDst (Data.pk i k 1))]⟩) = true := by decide +kernel

theorem pack_tags : ∀ (i : Fin 8) (k : Fin 4), ∀ p ∈ proQt (522 + 6 * i.val + k.val + 1),
    p.1 ≠ 747 + 5 * i.val + k.val ∧ (proQt (522 + 6 * i.val + k.val)).lookup p.1 = some p.2 := by
  decide +kernel

/-- **One pack** of two query halves into a word of a store. -/
theorem pack_step (i : Fin 8) (k : Fin 4) {F : List (Nat × Value)} {x y : Value}
    (hx : (qDst (Data.pk i k 0), x) ∈ F) (hy : (qDst (Data.pk i k 1), y) ∈ F)
    (bx : x.bytes = 2) (by' : y.bytes = 2) (hn : 747 + 5 * i.val + k.val ∉ F.map Prod.fst) :
    SegQ kernel Assumptions.all L g (QT proQt) (522 + 6 * i.val + k.val) F
      (522 + 6 * i.val + k.val + 1) ((747 + 5 * i.val + k.val, joinValue x y) :: F) :=
  move_seg (OItem.instrB_eq (pack_code i k)) rfl rfl (by omega) (by omega)
    (fun t hF => hex_pack hx hy bx by' t hF) (fun R hR => holds_update_cons hR hn)
    (pack_tags i k)


theorem qv_bytes (d : Data.D) (hv : ∀ k, (d.v.q k).bytes = 2) (m : Fin 64) :
    (Data.qv L g d m).bytes = 2 := by
  unfold Data.qv
  split
  · exact hv m
  · rfl

/-- The fact of a tag in the state `d`. -/
noncomputable abbrev tf (Q : Params) (L : Launch) (g : Nat) (d : Data.D) (τ : Data.Tag) : Nat ×
    Value := (τ.reg, τ.val Q L g d)

/-- **The four packs** of store `i`: the facts of its four words. -/
theorem packs4 (d : Data.D) (i : Fin 8) {F : List (Nat × Value)}
    (hq : ∀ (k : Fin 4) (b : Fin 2), tf Q L g d (.qh (Data.pk i k b)) ∈ F)
    (hv : ∀ k, (d.v.q k).bytes = 2) (hn : ∀ k : Fin 4, 747 + 5 * i.val + k.val ∉ F.map Prod.fst) :
    SegQ kernel Assumptions.all L g (QT proQt) (522 + 6 * i.val) F (526 + 6 * i.val)
      (tf Q L g d (.qw i 3) :: tf Q L g d (.qw i 2) :: tf Q L g d (.qw i 1) :: tf Q L g d (.qw i
          0) :: F) := by
  have st (k : Fin 4) {F' : List (Nat × Value)} (hF : ∀ p ∈ F, p ∈ F')
      (hn' : 747 + 5 * i.val + k.val ∉ F'.map Prod.fst) :
      SegQ kernel Assumptions.all L g (QT proQt) (522 + 6 * i.val + k.val) F'
        (522 + 6 * i.val + k.val + 1) (tf Q L g d (.qw i k) :: F') :=
    pack_step i k (hF _ (hq k 0)) (hF _ (hq k 1)) (qv_bytes d hv _) (qv_bytes d hv _) hn'
  have key (k : Fin 4) (j : Nat) (hj : j < k.val) : 747 + 5 * i.val + k.val ≠ 747 + 5 * i.val + j :=
    by omega
  refine SegQ.comp (b := 522 + 6 * i.val + 1) (G := tf Q L g d (.qw i 0) :: F) (st 0 (fun _ h =>
      h) (hn 0))
    (SegQ.comp (b := 522 + 6 * i.val + 2) (G := tf Q L g d (.qw i 1) :: tf Q L g d (.qw i 0) :: F)
    (st 1 (fun _ h => List.mem_cons_of_mem _ h) (by
      simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨by simp [Data.Tag.reg], hn 1⟩))
    (SegQ.comp (b := 522 + 6 * i.val + 3)
      (G := tf Q L g d (.qw i 2) :: tf Q L g d (.qw i 1) :: tf Q L g d (.qw i 0) :: F)
      (st 2 (fun _ h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)) (by
        simp only [List.map_cons, List.mem_cons, not_or]
        exact ⟨by simp [Data.Tag.reg], by simp [Data.Tag.reg], hn 2⟩)) ?_))
  have := st 3 (F' := tf Q L g d (.qw i 2) :: tf Q L g d (.qw i 1) :: tf Q L g d (.qw i 0) :: F)
    (fun _ h => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))
    (by
      simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨by simp [Data.Tag.reg], by simp [Data.Tag.reg], by simp [Data.Tag.reg], hn 3⟩)
  simpa [show 522 + 6 * i.val + 3 + 1 = 526 + 6 * i.val by omega] using this


/-- The registers of the data facts of the query region. -/
def qKeys : List Nat :=
  525 :: 199 :: List.range' 198 65 ++ (List.range' 747 39).filter fun r => (r - 747) % 5 < 4

theorem ldq_keys : ∀ j : Fin 64, ∀ τ ∈ Data.tags (.ldq j), τ.reg ∈ qKeys := by decide +kernel

theorem stq_keys : ∀ i : Fin 8, ∀ j : Fin 4, ∀ τ ∈ Data.tags (.stq i j), τ.reg ∈ qKeys := by
  decide +kernel

theorem mem_facts_sub {c : Control.D} {pc pc' : Nat} {q : Nat × Value}
    (hl : (ctlLive pc').isSublist (ctlLive pc) = true) (h : q ∈ facts Q L g w c pc') :
    q ∈ facts Q L g w c pc := by
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
  exact mem_factsFrom (val := valueOf Q L g w c) ((List.isSublist_iff_sublist.mp hl).subset hr)


theorem st0_tags : ∀ τ ∈ Data.tags (.stq 0 0), τ ∈ Data.tags (.ldq 63) ∨ τ = .qh 63 ∨
    ∃ k : Fin 4, τ = .qw 0 k := by decide +kernel

theorem st0_keys : (∀ k : Fin 4, 747 + k.val ∉ (Data.tags (.ldq 63)).map Data.Tag.reg ∧
    747 + k.val ∉ ctlLive 522 ∧ 747 + k.val ≠ qDst 63) ∧
    (ctlLive 526).isSublist (ctlLive 522) = true ∧
    (∀ k : Fin 4, ∀ b : Fin 2, Data.Tag.qh (Data.pk 0 k b) ∈ Data.tags (.ldq 63)) := by
  decide +kernel

/-- **From the last load to the first store**: the address, and the four packs. -/
theorem to_stq0 (c : Control.D) (v : Data.Vals) (x : Value) (hv : ∀ k, (v.q k).bytes = 2)
    (hx : Data.qv L g (dq c v (.ldq 63)) 63 = x) :
    SegQ kernel Assumptions.all L g (QT proQt) 515
      ((qDst 63, x) :: dFacts Q L g w (dq c v (.ldq 63))) 526
      (dFacts Q L g w (dq c v (.stq 0 0))) := by
  obtain ⟨hk, hl, hq⟩ := st0_keys
  let D := (qDst 63, x) :: Data.dF Q L g (dq c v (.ldq 63))
  refine SegQ.comp (b := 515) (G := D ++ facts Q L g w c 515) (SegQ.sub fun q hq' => ?_)
    (SegQ.comp (b := 522) (G := D ++ facts Q L g w c 522)
    (SegQ.of_seg_pre (Dk := qKeys) (fun p hp => ?_) Lib.rulesFrame (seg_first_addr (Q := Q) (w := w)
      (d := c)) rfl (by decide +kernel) (by decide +kernel)
      (PlainSegs.mono (plainSegs_pro (a := 27) (b := 574) le_rfl) (by decide +kernel)
        (by decide +kernel)) (by decide +kernel) (by decide +kernel))
    (SegQ.comp (b := 526) (G := _) (packs4 (dq c v (.ldq 63)) 0 (F := D ++ facts Q L g w c 522)
      (fun k b => List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_map_of_mem
        (f := fun τ => (τ.reg, τ.val Q L g (dq c v (.ldq 63)))) (hq k b)))) hv (fun k h => by
      obtain ⟨p, hp, he⟩ := List.mem_map.mp h
      rcases List.mem_append.mp hp with hp | hp
      · rcases List.mem_cons.mp hp with rfl | hp
        · exact (hk k).2.2 he.symm
        · obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp hp
          exact (hk k).1 (he ▸ List.mem_map_of_mem (f := Data.Tag.reg) hτ)
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
        exact (hk k).2.1 (he ▸ by simpa [facts, factsFrom_keys] using hr))) (SegQ.sub fun q hq' =>
            ?_)))
  · rcases List.mem_append.mp hq' with h | h
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ h)
    · exact List.mem_cons_of_mem _ (List.mem_append_right _
        (mem_facts_sub (c := c) (pc := 514) (by decide +kernel) h))
  · rcases List.mem_cons.mp hp with rfl | hp
    · exact (by decide +kernel : qDst 63 ∈ qKeys)
    · obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp hp
      exact ldq_keys 63 τ hτ
  · rcases List.mem_append.mp hq' with h | h
    · obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp h
      rw [tag_val_site (Q := Q) (L := L) (g := g) c v (.stq 0 0) (.ldq 63) τ]
      rcases st0_tags τ hτ with h1 | rfl | ⟨k, rfl⟩
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_cons_of_mem _
            (List.mem_map_of_mem (f := fun τ => (τ.reg, τ.val Q L g (dq c v (.ldq 63)))) h1))))))
      · have : Data.Tag.val Q L g (dq c v (.ldq 63)) (.qh 63) = x := hx
        rw [this]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_append_left _ List.mem_cons_self))))
      · fin_cases k <;> simp [tf]
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_append_right _ (mem_facts_sub hl h)))))

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
