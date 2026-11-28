-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.RefNext
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.LaunchReads
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Lemmas.Flow.MemTmpl

@[expose] public section

/-! # The two length loads read the row's lengths

-- domain: consistent

At a length load whose pointer is set (`SiteOk`), the event the state fires is the `.nc` read of
the row's four bytes (`read_topk`, `read_extra`); in a consistent execution the read returns the
row's length word (`ncReadOnly`, `Lib/LaunchReads.lean`), so the machine continues with that
word (`next_topk`, `next_extra`): it never stops at a length load. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- A set length pointer is the parameter's pointer. -/
theorem ptr_of_ne {b : Option Nat} (h : eqz64 (pw8 (b.getD 0)) = false) : ∃ x, b = some x := by
  cases b with
  | none => exact absurd h (by decide)
  | some x => exact ⟨x, rfl⟩

/-- The row's address word of a length array at `x`. -/
theorem row_word (hp : Pre P L m) {x : Nat} (hx : x + 4 * P.b ≤ 2 ^ 64) :
    add64 (pw8 x) (mulWide .u (r2W L g) 4) = W (x + 4 * ctaidY L g) := by
  have hr := (ctaid_lt hp g).2
  have hb := hp.bLt
  rw [show pw8 x = W x from pw8_eq x (by omega)]
  exact lenAddr_eq (by omega) (by omega)

/-- The read of a length load at register `base` holding the row's address in the array at `x`. -/
theorem read_at {t : TState} {e : Event} {o : Option TState} {pc base dst x row : Nat}
    (hpc : t.pc = pc) (hs : t.sub = 0) (hreg : t.regs base = some (b64 (x + 4 * row)))
    (hx : x + 4 * row < 2 ^ 64) (hal : x % 4 = 0) (hnc : ncLoads.contains pc = true)
    (hf : Fires pc (loadTmpl Assumptions.all L g t .global true 32 [dst] base 0) e o) :
    ∃ bs, ReadsLaunchWord e (x + 4 * row) bs := by
  have hA : Assumptions.all.any (·.ncLoads t.pc) = true := by
    have hm : pc ∈ ncLoads := by simpa using hnc
    rw [hpc]
    simp [Assumptions.all, Assumptions.ncReadOnly, Assumption.ncReadOnly, hm]
  rw [loadTmpl_global_nc hs hreg hx (by decide) (by omega) hA] at hf
  obtain ⟨bs, -, rfl, -⟩ := hf
  exact ⟨bs, rfl, hnc⟩

/-- **The top-k length load reads the row's word.** -/
theorem read_topk (hp : Pre P L m) {x : Nat} (hx : P.topkLenBase = some x)
    {l0 l1 neg cnt pha par : BitVec 64} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hat : (code P L g).AtD ⟨.loadTopk, l0, l1, neg, cnt, pha, par⟩ t)
    (hc : kernel.code[(code P L g).pc ⟨.loadTopk, l0, l1, neg, cnt, pha, par⟩]? = some ins)
    (hf : Fires ((code P L g).pc ⟨.loadTopk, l0, l1, neg, cnt, pha, par⟩)
      (eventTmpl Assumptions.all L g t ins.op) e o) :
    ∃ bs, ReadsLaunchWord e (x + 4 * ctaidY L g) bs := by
  obtain ⟨hpc, hs, -, -, hF⟩ := hat
  obtain ⟨-, hal, hrange⟩ := hp.topkLenAddressable x hx
  have hr := (ctaid_lt hp g).2
  have hreg := regs_of_factsFrom hF (r := 3054) (by show 3054 ∈ Flow.live 1876; decide)
  simp only [valueOf, values, valuesLens, List.lookup, hx, Option.getD_some] at hreg
  rw [row_word hp hrange] at hreg
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1876)
  exact read_at hpc hs hreg (by omega) hal (by show ncLoads.contains 1876 = true; decide) hf

/-- **The extra length load reads the row's word.** -/
theorem read_extra (hp : Pre P L m) {x : Nat} (hx : P.extraTopkLenBase = some x)
    {l0 l1 neg cnt pha par : BitVec 64} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hat : (code P L g).AtD ⟨.loadExtra, l0, l1, neg, cnt, pha, par⟩ t)
    (hc : kernel.code[(code P L g).pc ⟨.loadExtra, l0, l1, neg, cnt, pha, par⟩]? = some ins)
    (hf : Fires ((code P L g).pc ⟨.loadExtra, l0, l1, neg, cnt, pha, par⟩)
      (eventTmpl Assumptions.all L g t ins.op) e o) :
    ∃ bs, ReadsLaunchWord e (x + 4 * ctaidY L g) bs := by
  obtain ⟨hpc, hs, -, -, hF⟩ := hat
  obtain ⟨-, hal, hrange⟩ := hp.extraTopkLenAddressable x hx
  have hr := (ctaid_lt hp g).2
  have hreg := regs_of_factsFrom hF (r := 3056) (by show 3056 ∈ Flow.live 1886; decide)
  simp only [valueOf, values, valuesLens, List.lookup, hx, Option.getD_some] at hreg
  rw [row_word hp hrange] at hreg
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_1886)
  exact read_at hpc hs hreg (by omega) hal (by show ncLoads.contains 1886 = true; decide) hf

/-- A length load's word continues the machine. -/
theorem ncWord_word {e : Event} {f : BitVec 64 → D} {a : Acc} {bs : List (Option Byte)} {n : Nat}
    (hk : e.kind = .nc a bs) (hr : rebuild 3 bs = .ok (b32 n)) :
    ncWord e f = some (some (f (W n))) := by
  simp [ncWord, hk, hr, b32, W]

section
variable {X : Execution} {i : EvId} {l0 l1 neg cnt pha par : BitVec 64} {t : TState} {ins : Instr}
  {e : Event} {o : Option TState}
  (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hget : X.get i = some e)
include hp hX hget

/-- **The top-k length load continues with the row's length.** -/
theorem next_topk (hok : SiteOk P L g ⟨.loadTopk, l0, l1, neg, cnt, pha, par⟩)
    (hat : (code P L g).AtD ⟨.loadTopk, l0, l1, neg, cnt, pha, par⟩ t)
    (hc : kernel.code[(code P L g).pc ⟨.loadTopk, l0, l1, neg, cnt, pha, par⟩]? = some ins)
    (hf : Fires ((code P L g).pc ⟨.loadTopk, l0, l1, neg, cnt, pha, par⟩)
      (eventTmpl Assumptions.all L g t ins.op) e o) :
    succ P L g ⟨.loadTopk, l0, l1, neg, cnt, pha, par⟩ e =
      some (some (afterTopk P ⟨.loadTopk, l0, l1, neg, cnt, pha, par⟩
        (W (P.topkLen (ctaidY L g))))) := by
  obtain ⟨h1, -, -⟩ := hok
  obtain ⟨x, hx⟩ := ptr_of_ne (h1 rfl)
  obtain ⟨bs, hk, hpc⟩ := read_topk hp hx hat hc hf
  exact ncWord_word hk (rebuild_topk hp hX (ctaid_lt hp g).2 hx hget ⟨hk, hpc⟩)

/-- **The extra length load continues with the row's length.** -/
theorem next_extra (hok : SiteOk P L g ⟨.loadExtra, l0, l1, neg, cnt, pha, par⟩)
    (hat : (code P L g).AtD ⟨.loadExtra, l0, l1, neg, cnt, pha, par⟩ t)
    (hc : kernel.code[(code P L g).pc ⟨.loadExtra, l0, l1, neg, cnt, pha, par⟩]? = some ins)
    (hf : Fires ((code P L g).pc ⟨.loadExtra, l0, l1, neg, cnt, pha, par⟩)
      (eventTmpl Assumptions.all L g t ins.op) e o) :
    succ P L g ⟨.loadExtra, l0, l1, neg, cnt, pha, par⟩ e =
      some (some (lensD ⟨.loadExtra, l0, l1, neg, cnt, pha, par⟩ l0
        (W (P.extraTopkLen (ctaidY L g))))) := by
  obtain ⟨-, h2, -⟩ := hok
  obtain ⟨x, hx⟩ := ptr_of_ne (h2 rfl)
  obtain ⟨bs, hk, hpc⟩ := read_extra hp hx hat hc hf
  exact ncWord_word hk (rebuild_extra hp hX (ctaid_lt hp g).2 hx hget ⟨hk, hpc⟩)

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
