-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.MemoryWindows
public import Lemmas.Kernel.DecodeChunks
public import Kernels.FlashKdaFwd.Packed.Decode.Source

@[expose] public section
namespace FlashKda.Packed.Transfers
open PTX

theorem ok_of_some {α : Type} {d : Except String α} (h : d.toOption.isSome = true) :
    ∃ y, d = .ok y := by cases d <;> simp_all [Except.toOption]

theorem decode_suffix (env : Decode.Env) (xs : List Decode.SourceInstr) (width : Nat)
    (hw : 0 < width) (check : ∀ j, j*width < xs.length →
      (Decode.code env (j*width)
        ((xs.drop (j*width)).take (min width (xs.length - j*width)))).toOption.isSome = true)
    (j : Nat) : ∃ ys, Decode.code env (j*width) (xs.drop (j*width)) = .ok ys := by
  by_cases live : j*width < xs.length
  · let n := min width (xs.length - j*width)
    have bound : n ≤ (xs.drop (j*width)).length := by
      simp only [List.length_drop]
      exact Nat.min_le_right ..
    have positive : 0 < n := by unfold n; omega
    obtain ⟨a,ha⟩ := ok_of_some (check j live)
    have tail : ∃ b, Decode.code env (j*width + n) (xs.drop (j*width+n)) = .ok b := by
      by_cases full : width ≤ xs.length - j*width
      · have next : j*width + n = (j+1)*width := by simp [n, Nat.min_eq_left full, Nat.add_mul]
        rw [next]
        exact decode_suffix env xs width hw check (j+1)
      · have last : xs.length ≤ j*width+n := by unfold n; omega
        rw [List.drop_eq_nil_iff.mpr last]
        exact ⟨[], rfl⟩
    obtain ⟨b,hb⟩ := tail
    refine ⟨a ++ b, ?_⟩
    rw [← List.take_append_drop n (xs.drop (j*width))]
    apply Decode.code_append_ok ha
    rwa [List.length_take, Nat.min_eq_left bound, List.drop_drop]
  · rw [List.drop_eq_nil_iff.mpr (Nat.le_of_not_lt live)]
    exact ⟨[], rfl⟩
termination_by xs.length - j*width
decreasing_by rw [Nat.add_mul, Nat.one_mul]; omega

def finish (m : Except String Decode.Prepared) : Except String Kernel := do
  let p ← m
  return { p.header with code := ← Decode.code p.env 0 p.instrs }

def window (m : Except String Decode.Prepared) (pc n : Nat) : Option (List Instr) := do
  let p ← m.toOption
  (Decode.code p.env pc ((p.instrs.drop pc).take n)).toOption

theorem assemble {m : Except String Decode.Prepared} {total width : Nat} (hw : 0 < width)
    (length : m.toOption.map (fun p => p.instrs.length) = some total)
    (checks : ∀ j, j*width < total →
      (window m (j*width) (min width (total-j*width))).isSome = true) :
    (finish m).toOption.map (fun k => k.code.length) = some total := by
  cases m with
  | error e => cases length
  | ok p =>
    change some p.instrs.length = some total at length
    cases Option.some.inj length
    obtain ⟨code,h⟩ := decode_suffix p.env p.instrs width hw checks 0
    simp only [Nat.zero_mul, List.drop_zero] at h
    simp [finish, bind, Except.bind, h, pure, Except.pure, Except.toOption, decoded_length h]

private theorem combine {m : Except String Decode.Prepared} {total pc n k : Nat}
    {xs ys : List Instr} (count : m.toOption.map (fun p => p.instrs.length) = some total)
    (fits : pc+n ≤ total) (left : window m pc n = some xs) (right : window m (pc+n) k = some ys) :
    window m pc (n+k) = some (xs++ys) := by
  cases m with
  | error e => cases count
  | ok p =>
    change some p.instrs.length = some total at count
    cases Option.some.inj count
    have unwrap {d : Except String (List Instr)} {v : List Instr}
        (h : d.toOption = some v) : d = .ok v := by cases d <;> simp_all [Except.toOption]
    have a := unwrap (d := Decode.code p.env pc ((p.instrs.drop pc).take n)) left
    have b := unwrap (d := Decode.code p.env (pc+n) ((p.instrs.drop (pc+n)).take k)) right
    change (Decode.code p.env pc ((p.instrs.drop pc).take (n+k))).toOption = some (xs++ys)
    rw [List.take_add]
    have length : ((p.instrs.drop pc).take n).length = n := by simp; omega
    exact congrArg Except.toOption (Decode.code_append_ok a (by
      rw [length, List.drop_drop]; exact b))

theorem appendSlice {pc n k : Nat} {xs ys : List Instr} (fits : pc+n ≤ 3835)
    (left : slice pc n = some xs) (right : slice (pc+n) k = some ys) :
    slice pc (n+k) = some (xs++ys) := combine (m := prepared) source_count fits left right

theorem join {pc n k : Nat} (fits : pc+n ≤ 3835) (left : (slice pc n).isSome = true)
    (right : (slice (pc+n) k).isSome = true) : (slice pc (n+k)).isSome = true := by
  obtain ⟨xs,a⟩ := Option.isSome_iff_exists.mp left
  obtain ⟨ys,b⟩ := Option.isSome_iff_exists.mp right
  rw [appendSlice fits a b]
  rfl

end FlashKda.Packed.Transfers
