-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerOutEvents

@[expose] public section

/-! # The output tile of a consumer's TMA store

A TMA store with two coordinate registers holding 32-bit values below `2 ^ 31` has those values as
its box's origin (`fires_store_origin`). Slice `k`'s TMA store of a consumer at tile `(m, n)`
starts at column `256 n + 32 k` and row `512 m + 128 q + 256 r`, for the thread's warp group `q`
and its CTA's rank `r` in the cluster (`tma_origin`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- A 32-bit value below `2 ^ 31` reads back as itself. -/
theorem toInt_ofNat_small {v : Nat} (h : v < 2 ^ 31) : (BitVec.ofNat 32 v).toInt = v := by
  rw [BitVec.toInt_ofNat']
  rw [Int.bmod_def]
  have h1 : ((v : Int) % (2 ^ 32 : Nat)) = v := by
    rw [Int.emod_eq_of_lt (by omega) (by push_cast; omega)]
  push_cast at h1 ⊢
  rw [h1]
  split_ifs with h2
  · rfl
  · exfalso; omega

/-- **A TMA store's origin** is the values of its two coordinate registers. -/
theorem fires_store_origin {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {map : Opnd}
    {r0 r1 src : Nat} {off : Int} {policy : Option Opnd} {mode : TensorMode}
    {reduce : Option AtomOp} {pc : Nat} {e : Event} {o : Option TState} {v0 v1 : Nat}
    (hf : Fires pc (eventTmpl A L g t (.cpTensorStore map [.reg r0, .reg r1] src off policy mode
      reduce)) e o)
    (h0 : t.regs r0 = some (b32 v0)) (h1 : t.regs r1 = some (b32 v1)) (hv0 : v0 < 2 ^ 31)
    (hv1 : v1 < 2 ^ 31) :
    ∀ a s, e.kind = .tensorStore a s → (mode = .tile → s.rows = none) ∧ s.reduce = reduce ∧
      ∀ i : Fin (s.outer + 1),
        s.origin i = if i.val = 0 then (v0 : Int) else if i.val = 1 then (v1 : Int) else 0 := by
  intro a s hk
  simp only [eventTmpl, tensorStoreTmpl] at hf
  cases hs : tensorStoreSpec L g t map [.reg r0, .reg r1] src off policy mode reduce with
  | error f =>
    simp only [hs, bind, Except.bind, ofExec, Fires] at hf
    rw [hf.1] at hk
    cases hk
  | ok r =>
    obtain ⟨a', s'⟩ := r
    simp only [hs, bind, Except.bind, pure, Except.pure, ofExec, Fires] at hf
    rw [hf.1] at hk
    cases hk
    unfold tensorStoreSpec at hs
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      List.mapM_cons, List.mapM_nil, readBits_b32 h0 (by omega), readBits_b32 h1 (by omega)] at hs
    rcases hm : tensorMap L g t map [.reg r0, .reg r1] mode with f | ⟨a'', outer, d⟩ <;>
      rw [hm] at hs
    · cases hs
    rcases hsrc : sharedEffAddr L g t false src off with f | sl <;> simp only [hsrc] at hs
    all_goals repeat' (split at hs <;> (try (cases hs; done)))
    all_goals cases hs
    all_goals refine ⟨fun h => by subst h; rfl, rfl, fun i => ?_⟩
    all_goals rcases i with ⟨_ | _ | i, hi⟩
    all_goals simp
    all_goals first
      | (rw [Nat.mod_eq_of_lt (by omega)]; exact toInt_ofNat_small hv0)
      | (rw [Nat.mod_eq_of_lt (by omega)]; exact toInt_ofNat_small hv1)

namespace Consumer

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

set_option maxHeartbeats 8000000 in
/-- **The origin of slice `k`'s TMA store**: column `256 n + 32 k`, row `512 m + 128 q + 256 r`. -/
theorem tma_origin {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hat : (code L g).AtD (.inr (.cons d)) t) (hi : Inv d) (htid : tidOf L g < 256)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) {k : Fin 8} (hs : d.site = .tma k) :
    ∀ a s, e.kind = .tensorStore a s → s.rows = none ∧ s.reduce = none ∧ ∀ i : Fin (s.outer + 1),
      s.origin i = if i.val = 0 then ((256 * d.n + 32 * k.val : Nat) : Int)
        else if i.val = 1 then
          ((512 * d.m + 128 * (tidOf L g / 32 / 4) + 256 * (g / L.block % 2) : Nat) : Int)
        else 0 := by
  have hm := hi.m
  have hn := hi.n
  have hq : tidOf L g / 32 / 4 < 2 := by omega
  have hr : g / L.block % 2 < 2 := Nat.mod_lt _ (by norm_num)
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs hc hf hat hm hn ⊢
  subst hs
  intro a s hk
  obtain ⟨kv, hkv⟩ : ∃ kv, kv = k.val := ⟨_, rfl⟩
  have hk32 : kv < 8 := hkv ▸ k.isLt
  rw [← hkv]
  fin_cases k <;> code_at hc <;> subst hc <;>
    obtain ⟨hrow, hred, ho⟩ := fires_store_origin (v0 := 256 * n + 32 * kv)
      (v1 := 512 * mm + 128 * (tidOf L g / 32 / 4) + 256 * (g / L.block % 2)) hf
      ((holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by cons_values; simp [hkv])))
      ((holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by cons_values)))
      (by omega) (by omega) a s hk <;>
    exact ⟨hrow rfl, hred, ho⟩

end Consumer

end

end PTX.Kernels.Fp16Gemm8192.Proof
