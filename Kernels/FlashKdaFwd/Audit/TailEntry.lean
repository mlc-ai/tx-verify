-- SPDX-License-Identifier: Apache-2.0
import Kernels.FlashKdaFwd.Audit.TailPath

/-! Lift a register replay to the fully decoded production entry and identify the unique
clearing thread for each byte of each inactive key row. -/
namespace FlashKda.Tail
open PTX
noncomputable section

def whole (mode : Bool) := Decode.kernelIn Generated.FlashKdaFwd.module.globals
    Generated.FlashKdaFwd.module.functions[if mode then 1 else 9]!

private theorem map_length {α β : Type} (f : α → Except String β) {xs : List α} {ys : List β}
    (h : xs.mapM f = .ok ys) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil =>
    simpa [List.mapM_nil, pure, Except.pure] using congrArg List.length (Except.ok.inj h).symm
  | cons x xs ih =>
    simp only [List.mapM_cons] at h
    cases a : f x <;> simp [a,bind,Except.bind,pure,Except.pure] at h
    cases b : List.mapM f xs <;> simp [b] at h
    subst ys
    simp [ih b]

private theorem decoded_length {env : Decode.Env} {pc} {xs} {ys}
    (h : Decode.code env pc xs = .ok ys) : ys.length = xs.length := by
  simpa using map_length _ h

private theorem divide {env : Decode.Env} {pc} {xs zs} {ys}
    (h : Decode.code env pc (xs ++ zs) = .ok ys) :
    ∃ a b, Decode.code env pc xs = .ok a ∧ Decode.code env (pc+xs.length) zs = .ok b ∧
      ys = a ++ b ∧ a.length = xs.length := by
  have joined : Decode.code env pc (xs ++ zs) =
      (do
        let a ← Decode.code env pc xs
        let b ← Decode.code env (pc+xs.length) zs
        pure (a++b)) := by
    simp only [Decode.code,List.zipIdx_append,List.mapM_append]
  rw [joined] at h
  cases a : Decode.code env pc xs <;> simp [a,bind,Except.bind,pure,Except.pure] at h
  cases b : Decode.code env (pc+xs.length) zs <;> simp [b] at h
  exact ⟨_,_,rfl,rfl,h.symm,decoded_length a⟩

theorem slice_of_decoding {env : Decode.Env} {xs ys} {s n : Nat} (fits : s+n ≤ xs.length)
    (h : Decode.code env 0 xs = .ok ys) :
    Decode.code env s ((xs.drop s).take n) = .ok ((ys.drop s).take n) := by
  have left : (xs.take s).length = s := by simp; omega
  have mid : ((xs.drop s).take n).length = n := by simp; omega
  rw [← List.take_append_drop s xs] at h
  obtain ⟨a,b,_,hb,rfl,ha⟩ := divide h
  rw [left] at ha
  simp only [left, Nat.zero_add] at hb
  rw [← List.take_append_drop n (xs.drop s)] at hb
  obtain ⟨c,d,hc,_,rfl,hs⟩ := divide hb
  rw [mid] at hs
  rw [← ha, List.drop_left, ← hs, List.take_left]
  rw [ha,hs]
  exact hc

theorem actual_slice (mode : Bool) {k : Kernel} (h : whole mode = .ok k) :
    (k.code.drop (start mode)).take (finish mode-start mode) = body mode := by
  let m := Generated.FlashKdaFwd.module
  let f := m.functions[if mode then 1 else 9]!
  change Decode.kernelIn m.globals f = .ok k at h
  unfold Decode.kernelIn at h
  cases prep : Decode.prepare m.globals f with
  | error e => simp [prep,bind,Except.bind] at h
  | ok p =>
    cases hc : Decode.code p.env 0 p.instrs with
    | error e => simp [prep,hc,bind,Except.bind] at h
    | ok is =>
      simp only [prep,hc,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at h
      subst k
      have frozen := decoded mode
      change ((Decode.prepare m.globals f).toOption.bind fun p =>
        (Decode.code p.env (start mode)
          ((p.instrs.drop (start mode)).take (finish mode-start mode))).toOption) = _ at frozen
      rw [prep] at frozen
      cases hs : Decode.code p.env (start mode)
          ((p.instrs.drop (start mode)).take (finish mode-start mode)) with
      | error e => simp [Except.toOption,hs] at frozen
      | ok middle =>
        simp [Except.toOption,hs] at frozen
        subst middle
        have len := decoded_length hs
        have bodyLen : (body mode).length = finish mode - start mode := by cases mode <;> rfl
        rw [bodyLen,List.length_take,List.length_drop] at len
        have valid : start mode < finish mode := by cases mode <;> decide
        have slice := slice_of_decoding (s := start mode) (n := finish mode-start mode)
          (by omega) hc
        exact (Except.ok.inj (slice.symm.trans hs))

theorem entry_trace (mode : Bool) (k : Kernel) (h : whole mode = .ok k)
    (live col : Nat) (ok : traceMatches mode live col = true) :
    ∃ last, last.pc = finish mode ∧ Relation.ReflTransGen (advancing k (128+col))
      (entryState mode live col, expected live col) (last,[]) := by
  apply reaches mode k _ 82
  rw [same_trace]
  · exact of_decide_eq_true ok
  · intro pc lo hi
    have hs := actual_slice mode h
    change k.code[pc]? =
      (List.replicate (start mode) (⟨none,.ret⟩ : Instr) ++ body mode)[pc]?
    rw [List.getElem?_append_right (by simpa only [List.length_replicate] using lo),
      List.length_replicate, ← hs, List.getElem?_take_of_lt (by omega), List.getElem?_drop]
    congr 1
    omega

/-- Across all threads, a byte of a live row is untouched. Each byte of an inactive
row belongs to exactly the store of the thread for that column. -/
theorem touches_iff (live : Nat) (row : Fin 16) (col owner : Fin 128) (j : Fin 2) :
    (∃ a ∈ expected live owner,
      let byte := launch.sharedBase + 4096 + row.val*256 + 2*col.val + j.val
      a ≤ byte ∧ byte < a+2) ↔ live ≤ row.val ∧ owner = col := by
  simp only [expected, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨a, ⟨r,hr,rfl⟩,lo,hi⟩
    have sameRow : live+r = row.val := by
      by_contra! different
      rcases lt_or_gt_of_ne different with h|h <;> omega
    constructor
    · omega
    · apply Fin.ext
      omega
  · rintro ⟨h,rfl⟩
    refine ⟨_,⟨row.val-live,by omega,rfl⟩,?_,?_⟩ <;> omega

end
end FlashKda.Tail
