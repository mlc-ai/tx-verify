-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SharedSym
public import Lemmas.Flow.MemTmpl

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow

variable {L : Launch} {g pc : Nat} {A : List Assumption} {t : TState} {e : Event}

/-- The 32-bit wrap of `x + n` as the address of a shared symbol plus an offset is its residue. -/
theorem wrapAddr32_ofNat (x n : Nat) :
    wrapAddr 32 (BitVec.ofNat 64 x) (n : Int) = (x + n) % 2 ^ 32 := by
  simp only [wrapAddr, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
  have h : ((n : Int) % ((2 ^ 64 : Nat) : Int)).toNat = n % 2 ^ 64 := by
    omega
  rw [h]
  omega

/-- The footprint of a plain four-byte access at `l`, element `elem` of its vector access. -/
def wordAcc (l : Loc) (elem : Nat := 0) : Acc := { loc := l, size := 4, elem := elem }

/-- `st.shared.v<vec>.b32 [global_smem + off], {srcs}`, as the decoder gives it. -/
def symStore (vec : Nat) (off : Int) (srcs : List Opnd) : MemAccess :=
  { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int .b 32, vec := vec,
    addr := { base := .sharedSym 0, off := off }, srcs := srcs }

theorem symStore_rule {vec : Nat} {off : Int} {srcs : List Opnd} (hl : srcs.length = vec)
    (hv : vec = 1 ∨ vec = 2 ∨ vec = 4) : (symStore vec off srcs).rule = some .threadAccess := by
  unfold symStore
  rcases hv with rfl | rfl | rfl <;> simp [MemAccess.rule, memTypeOk, DType.width, hl]

theorem symStore_loc (vec : Nat) (off : Int) (srcs : List Opnd) :
    (symStore vec off srcs).locSpace? = none := rfl

/-- **A store to a shared symbol plus an offset** writes element `j` (the thread's sub-step) of its
vector access: four bytes `storeValue 32` of the element's source, at `sharedBase + off + 4 j`
(modulo `2 ^ 32`) of the thread's CTA. -/
theorem fires_st_sym {vec j : Nat} {off : Int} {srcs : List Opnd} {o : Opnd} {v : Value}
    {u : TState} {op : Op} (hop : op = .mem (symStore vec off srcs)) (hoff : 0 ≤ off)
    (hsub : t.sub = j) (ho : srcs[j]? = some o)
    (hv : readValue L g t 32 o = .ok v)
    (hl : srcs.length = vec) (hvec : vec = 1 ∨ vec = 2 ∨ vec = 4)
    (hf : Fires pc (eventTmpl A L g t op) e (some u)) :
    ∃ v', storeValue 32 v = .ok v' ∧
      e = ⟨pc, .wr (wordAcc ⟨.shared, g / L.block, (L.sharedBase + off.toNat) % 2 ^ 32 + 4 * j⟩ j)
        v'.toBytes⟩ := by
  subst hop
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hoff
  simp only [Int.toNat_natCast]
  have hm : memTmpl A L g t (symStore vec (n : Int) srcs) =
      accessTmpl A L g t (symStore vec (n : Int) srcs) := by
    simp [memTmpl, symStore_rule hl hvec, symStore_loc]
  simp only [eventTmpl] at hf
  change Fires pc (memTmpl A L g t (symStore vec (n : Int) srcs)) e (some u) at hf
  rw [hm] at hf
  simp only [accessTmpl, symStore] at hf
  rw [accessAcc_of_weak rfl] at hf
  have hw : wrapAddr 32 (BitVec.ofNat 64 (L.sharedBase + 0)) (n : Int) =
      (L.sharedBase + 0 + n) % 2 ^ 32 := wrapAddr32_ofNat (L.sharedBase + 0) n
  simp only [accessLoc, pure, Except.pure, bind, Except.bind, hsub, elemAcc, hw] at hf
  simp [DType.width, ho, hv, CacheHints.globalOnly] at hf
  have hv8 : vec ≠ 8 := by rcases hvec with rfl | rfl | rfl <;> decide
  simp only [hv8, ↓reduceIte] at hf
  by_cases hal : (L.sharedBase + n) % 4294967296 % (4 * vec) = 0
  · simp only [hal, ↓reduceIte] at hf
    rcases hsv : storeValue 32 v with f | v'
    · simp only [hsv, Fires] at hf
      exact absurd hf.2 (by simp)
    · simp only [hsv, Fires, Loc.at] at hf
      exact ⟨v', rfl, by rw [hf.1]; rfl⟩
  · simp only [hal, ↓reduceIte, throw, throwThe, MonadExceptOf.throw, Fires] at hf
    exact absurd hf.2 (by simp)

end PTX.Kernels.InklingRelDecode.Proof.Lib
