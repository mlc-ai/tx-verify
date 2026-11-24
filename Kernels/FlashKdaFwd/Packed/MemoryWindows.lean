-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Transfers

@[expose] public section
namespace FlashKda.Packed.Transfers
open PTX

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

private theorem from_decode {k : Kernel} {globals : List (List String)} {f : Syntax.Function}
    (pc len : Nat) (h : Decode.kernelIn globals f = .ok k) (fits : pc + len ≤ k.code.length) :
    ((Decode.prepare globals f).toOption.bind fun p =>
      (Decode.code p.env pc ((p.instrs.drop pc).take len)).toOption) =
        some ((k.code.drop pc).take len) := by
  unfold Decode.kernelIn at h
  cases hp : Decode.prepare globals f with
  | error e => simp [hp, bind, Except.bind] at h
  | ok p =>
    cases hc : Decode.code p.env 0 p.instrs with
    | error e => simp [hp, hc, bind, Except.bind] at h
    | ok is =>
      simp only [hp, hc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst k
      change pc + len ≤ is.length at fits
      rw [decoded_length hc] at fits
      exact congrArg Except.toOption (slice_of_decoding fits hc)

set_option maxRecDepth 60000 in
theorem from_whole {k : Kernel} (pc len : Nat)
    (h : Decode.kernelIn Generated.FlashKdaPacked.module.globals
      Generated.FlashKdaPacked.module.functions[0]! = .ok k)
    (fits : pc + len ≤ k.code.length) :
    slice pc len = some ((k.code.drop pc).take len) :=
  @from_decode k Generated.FlashKdaPacked.module.globals
    Generated.FlashKdaPacked.module.functions[0]! pc len h fits

end FlashKda.Packed.Transfers
