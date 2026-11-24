-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Execution.ExecutionGrowth

@[expose] public section

/-! Initial contents are fixed per address, even when the launch specification leaves
those contents unspecified. These are consequences of reads-from, not new assumptions. -/
namespace PTX
noncomputable section

/-- An allocated W0 read returns a byte, including when its value was unspecified. -/
theorem initial_read_byte {mem0 : Mem0} {X : Execution} (hrf : RfWf mem0 X)
    {e : AsyncCopy.Ref} {a : Acc} {bs : List (Option Byte)} (he : X.MemReads e a bs)
    {k : Nat} (hk : k < a.size) (hs : X.rf e k = none)
    {c : Option Byte} (hc : mem0 (a.loc.at k) = some c) :
    bs[k]? = some (X.initialByte c (a.loc.at k)) := by
  have h := (hrf e a bs he).2 k hk
  rw [hs] at h
  exact h c hc

/-- Two reads from W0 of one allocated address return the same byte. -/
theorem initial_reads_agree {mem0 : Mem0} {X : Execution} (hrf : RfWf mem0 X)
    {e f : AsyncCopy.Ref} {a b : Acc} {xs ys : List (Option Byte)}
    (he : X.MemReads e a xs) (hf : X.MemReads f b ys) {i j : Nat}
    (hi : i < a.size) (hj : j < b.size) (he0 : X.rf e i = none) (hf0 : X.rf f j = none)
    (hl : a.loc.at i = b.loc.at j) {c : Option Byte}
    (hc : mem0 (a.loc.at i) = some c) : xs[i]? = ys[j]? := by
  rw [initial_read_byte hrf he hi he0 hc,
    initial_read_byte hrf hf hj hf0 (hl ▸ hc), hl]

/-- Growth cannot change an unspecified initial byte after a read observed it. Choices
at as-yet unobserved addresses need not be fixed by a finite execution prefix. -/
theorem initial_choice_preserved {mem0 : Mem0} {X Y : Execution}
    (hx : RfWf mem0 X) (hy : RfWf mem0 Y) (hle : X.le Y)
    {e : AsyncCopy.Ref} {a : Acc} {bs : List (Option Byte)} (he : X.MemReads e a bs)
    {k : Nat} (hk : k < a.size) (hs : X.rf e k = none)
    (hc : mem0 (a.loc.at k) = some none) : X.initial (a.loc.at k) = Y.initial (a.loc.at k) := by
  have hsY : Y.rf e k = none := (hle.2.1 e k ⟨a, bs, he⟩).trans hs
  have hvX := initial_read_byte hx he hk hs hc
  have hvY := initial_read_byte hy (Execution.le_memReads hle he) hk hsY hc
  exact Option.some.inj (Option.some.inj (hvX.symm.trans hvY))

end
end PTX
