-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Source.LocalOwned
public import Lemmas.Protocol.LocalMemory

@[expose] public section

/-! # The source of a byte of a local read

A `.local` read of thread `g` whose byte `k` an earlier write of `g` covers returns, at that byte,
the byte of an earlier write of `g` that covers it: the model forbids the initial memory
(`Hidden`, since the covering write precedes the read in thread order), a write of another thread
(local memory is the thread's own, `Frame.localOwned`) and a later write of `g` (`NoFuture`).
Unlike `local_read_byte_of_last_store`, it names no last store: every earlier write of the thread
that may be the source is a candidate, so a kernel concludes from a property every such write has
(for example that it writes the bytes of an integer: `WordByte`, `rebuild_word4`). Promoted
from tml-fa4's `Proof2/Lib/LocalSrc.lean`. -/

namespace PTX.Frame

open PTX

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A byte of a local read comes from an earlier covering write of the reading thread**, when
one exists. -/
theorem local_read_src (hX : Consistent L K A mem0 X) {g e k w : Nat} {a dst : Acc}
    {bs : List (Option Byte)} {written : List Byte}
    (hr : X.Reads (g, e) a bs) (hl : a.loc.space = .local) (hg : a.loc.cta = g)
    (hk : k < a.size) (hw : X.Writes (g, w) dst written) (hwe : w < e)
    (hc : dst.Covers (a.loc.at k)) :
    ∃ j dst' bytes, j < e ∧ X.MemWrites (.thread (g, j)) dst' bytes ∧
      dst'.Covers (a.loc.at k) ∧ bs[k]? = some (wbyte dst' bytes (a.loc.at k)) := by
  have hwa : X.Access (g, w) dst true := Or.inr (Or.inl ⟨written, hw, rfl⟩)
  have hra : X.Access (g, e) a false := Or.inl ⟨bs, hr, rfl⟩
  have hca := Acc.covers_at hk
  have hh := hX.hidden (.thread (g, e)) a bs k (.thread (g, w)) dst written (Or.inl hr) hk
    (Or.inl hw) hc
    (.direct (.inl (.single (.inl (po_of_overlap hwa hra rfl hwe ⟨a.loc.at k, hc, hca⟩)))))
  have hrf := (hX.rf (.thread (g, e)) a bs (Or.inl hr)).2 k hk
  cases hs : X.rf (.thread (g, e)) k with
  | none => simp [hs] at hh
  | some source =>
    rw [hs] at hrf
    obtain ⟨dst', bytes, hsource, hcov, hvalue⟩ := hrf
    have hlk : (a.loc.at k).space = .local := by simpa [Loc.at] using hl
    have hcta : (a.loc.at k).cta = g := by simpa [Loc.at] using hg
    obtain ⟨j, hj, ha⟩ := localOwned hX source dst' bytes _ hsource hlk hcov
    rw [hcta] at hj ha
    subst hj
    refine ⟨j, dst', bytes, ?_, hsource, hcov, hvalue⟩
    rcases Nat.lt_trichotomy j e with hje | rfl | hej
    · exact hje
    · exfalso
      obtain ⟨pc, hpc⟩ := hr
      rcases ha with ⟨_, -, hf⟩ | ⟨_, ⟨pc', h'⟩, -⟩ | ⟨_, _, ⟨pc', h'⟩⟩
      · cases hf
      · rw [hpc] at h'; cases h'
      · rw [hpc] at h'; cases h'
    · exact (hX.noFuture (.thread (g, e)) a bs k (.thread (g, j)) (Or.inl hr) hk hs
        (.direct (.inl (.single (.inl (po_of_overlap hra ha rfl hej
          ⟨a.loc.at k, hca, hcov⟩)))))).elim

end PTX.Frame

namespace PTX

/-- A byte of a 32-bit or 64-bit integer value, or nothing. -/
def WordByte (b : Option Byte) : Prop :=
  b = none ∨ ∃ w x i, b = some (.bits w x, i) ∧ (w = 32 ∨ w = 64)

/-- **Four bytes of 32-bit or 64-bit integers rebuild to a 32-bit word**, or do not rebuild. -/
theorem rebuild_word4 {bs : List (Option Byte)} (hl : bs.length = 4) (h : ∀ b ∈ bs, WordByte b) :
    (∃ x, rebuild 3 bs = .ok (.bits 32 x)) ∨ ∃ er, rebuild 3 bs = .error er := by
  have hhalves : ∀ fuel, (∃ x, rebuild.halves fuel bs = .ok (.bits 32 x)) ∨
      ∃ er, rebuild.halves fuel bs = .error er := by
    intro fuel
    unfold rebuild.halves
    by_cases hn : none ∈ bs
    · simp only [hn, ↓reduceIte]
      exact .inr ⟨_, rfl⟩
    have hall : bs.all intByte = true := by
      rw [List.all_eq_true]
      intro b hb
      rcases h b hb with rfl | ⟨w, x, i, rfl, -⟩
      · exact absurd hb hn
      · rfl
    simp only [hn, ↓reduceIte, hall, true_or]
    unfold rebuildBits
    cases hx : littleEndianBits bs with
    | none => exact .inr ⟨_, rfl⟩
    | some x => exact .inl ⟨BitVec.ofNat 64 x, by simp [hl]; rfl⟩
  unfold rebuild
  split
  · rename_i v rest
    split
    · rename_i hc
      rcases h _ (List.mem_cons_self ..) with hb | ⟨w, x, i, hb, hw⟩
      · cases hb
      · simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, -⟩ := hb
        rcases hw with rfl | rfl
        · exact .inl ⟨x, rfl⟩
        · simp [Value.bytes, hl] at hc
    · exact hhalves 2
  · exact hhalves 2

end PTX
