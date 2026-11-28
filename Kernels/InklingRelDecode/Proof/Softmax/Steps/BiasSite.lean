-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Steps.Base
public import Lemmas.Flow.Step.GuardedLoadU

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
open PTX PTX.Flow PTX.Proof

/-- The two guarded bias streams share a load shape and control flow. Their address and
destination families have different decoder ids. -/
inductive Bias where
  | pre | nxt
  deriving DecidableEq

def Bias.site : Bias → Fin 64 → Site
  | .pre => .pre
  | .nxt => .nxt

def Bias.guard : Bias → Nat
  | .pre => 85
  | .nxt => 92

def Bias.dst (b : Bias) (j : Fin 64) : Nat :=
  match b with
  | .pre => 263+j.val
  | .nxt => if j.val = 0 then 332 else 333+j.val

private def activeLoad (pc pred dst : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨some (p,false),.mem a⟩ =>
    p == pred && a.kind == .load && !a.nc && a.ext == .same &&
      a.regs == [dst] && !(Op.mem a).isLocal
  | _ => false

private theorem pre_load : ∀ j, activeLoad (Bias.pre.site j).pc 85 (Bias.pre.dst j) := by
  decide +kernel

private theorem next_load : ∀ j, activeLoad (Bias.nxt.site j).pc 92 (Bias.nxt.dst j) := by
  decide +kernel

theorem Bias.load (b : Bias) (j : Fin 64) :
    ∃ a : MemAccess, kernel.code[(b.site j).pc]? = some ⟨some (b.guard,false),.mem a⟩ ∧
      a.kind = .load ∧ a.nc = false ∧ a.ext = .same ∧ a.regs = [b.dst j] ∧
      (Op.mem a).isLocal = false := by
  have h : activeLoad (b.site j).pc b.guard (b.dst j) :=
    match b with | .pre => pre_load j | .nxt => next_load j
  unfold activeLoad at h
  split at h
  · rename_i p a hi
    simp only [Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨⟨hp,hk⟩,hn⟩,he⟩,hr⟩,hl⟩ := h
    exact ⟨a,hp ▸ hi,hk,hn,he,hr,hl⟩
  · cases h

private theorem pred_live : ∀ (b : Bias) j, b.guard ∈ Flow.live (b.site j).pc := by
  intro b; cases b <;> decide +kernel

private theorem data_dst : ∀ (b : Bias) j, ctl (b.dst j) = false := by
  intro b; cases b <;> decide +kernel

theorem Bias.free (b : Bias) (j : Fin 64) {e L g d} :
    b.dst j ∉ (facts e L g d (b.site j).pc).map Prod.fst := by
  rw [facts,factsFrom_keys]
  intro hm
  have h := (List.mem_filter.mp hm).2
  rw [data_dst] at h
  contradiction

theorem Bias.active {e L g i v} (b : Bias) (j : Fin 64)
    (hi : Inv e (g % L.block) ⟨b.site j,i,v⟩) :
    Code.GuardTrue (facts e L g ⟨b.site j,i,v⟩ (b.site j).pc) (some (b.guard,false)) := by
  apply Code.guardTrue_factsFrom
  · exact List.mem_filter.mpr ⟨pred_live b j,by cases b <;> decide⟩
  · cases b with
    | pre =>
      change Value.pred (preEnabled e (g % L.block)) = .pred true
      rw [(hi.pre j rfl).2]
    | nxt =>
      change Value.pred (nextEnabled e (g % L.block) i) = .pred true
      rw [hi.nxt j rfl]

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Control
