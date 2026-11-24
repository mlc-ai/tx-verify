-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.MemTmpl
public import Lemmas.Flow.Events

@[expose] public section

/-!
# Shared-memory, mbarrier and bulk-copy instructions

The event templates of shared loads, mbarrier operations and bulk copies, from register
facts.
-/

namespace PTX.Proof
open PTX

section
variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState}

theorem loadTmpl_shared {d base : Nat} {w a : Nat} (hs : t.sub = 0)
    (h : t.regs base = some (b32 a)) (ha : a < 2 ^ 32) (hw : 0 < w / 8) (hal : a % (w / 8) = 0) :
    loadTmpl A L g t .shared false w [d] base 0 =
      .read { loc := ⟨.shared, g / L.block, a⟩, size := w / 8 } (afterLoad t [d]) := by
  unfold loadTmpl
  rw [Flow.effAddr_b32 h ha]
  simp only [bind, Except.bind, List.length_singleton, hs]
  rw [elemAcc_ok hw (by simpa using hal)]
  simp [Loc.at, Bool.false_eq_true, ↓reduceIte]

theorem readBits_imm {n : Nat} (hn : n < 2 ^ 32) :
    readBits L g t 32 (.imm n) = .ok (BitVec.ofNat 64 n) := by
  have h64 : n < 18446744073709551616 := by omega
  have h32 : n < 4294967296 := by simpa using hn
  simp only [readBits, truncBits, pure, Except.pure]
  congr 2
  rw [show (BitVec.ofInt 64 (n : Int)) = BitVec.ofNat 64 n from by
    apply BitVec.eq_of_toNat_eq; simp [Nat.mod_eq_of_lt h64]]
  simp [Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt h32]

theorem tma_mbarInit {r : Nat} {a n : Nat} (h : t.regs r = some (b32 a)) (ha : a < 2 ^ 32)
    (hal : a % 8 = 0) (hn : 0 < n) (hn' : n < 2 ^ 20) :
    tmaTmpl L g t (.mbarInit r 0 (.imm n)) = .mbInit ⟨.shared, g / L.block, a⟩ n (next t) := by
  simp only [tmaTmpl, Flow.mbarLoc_b32 h ha hal, readBits_imm (show n < 2 ^ 32 by omega), bind,
    Except.bind, Proof.toNat_ofNat_lt (show n < 2 ^ 64 by omega)]
  have h20 : n < 1048576 := by simpa using hn'
  simp [ofExec, hn, h20, pure, Except.pure]

theorem tma_arrive {r : Nat} {a n : Nat} (h : t.regs r = some (b32 a)) (ha : a < 2 ^ 32)
    (hal : a % 8 = 0) (hn' : n < 2 ^ 32) :
    tmaTmpl L g t (.mbarArrive r 0 (.imm n)) = .arrive ⟨.shared, g / L.block, a⟩ n (next t) := by
  simp only [tmaTmpl, Flow.mbarLoc_b32 h ha hal, readBits_imm (show n < 2 ^ 32 by omega), bind,
    Except.bind, Proof.toNat_ofNat_lt (show n < 2 ^ 64 by omega)]
  rfl

theorem tma_cpBulk {rd rs rm : Nat} {d s m n : Nat} (hd : t.regs rd = some (b32 d))
    (hda : d < 2 ^ 32) (hs : t.regs rs = some (b64 s)) (hsa : s < 2 ^ 64)
    (hm : t.regs rm = some (b32 m)) (hma : m < 2 ^ 32) (hmal : m % 8 = 0) (hn : 0 < n)
    (hn' : n < 2 ^ 32) (hn16 : n % 16 = 0) (hd16 : d % 16 = 0) (hs16 : s % 16 = 0)
    (hr : bulkRangeOk n ⟨.shared, g / L.block, d⟩ ⟨.global, 0, s⟩) :
    tmaTmpl L g t (.cpBulk (BulkCopy.mk .globalToCta rd 0 rs 0 (.imm n) (some (rm, 0)) none none
        none none none none)) =
      .copy (bulkSpec { loc := ⟨.global, 0, s⟩, size := n }
        { loc := ⟨.shared, g / L.block, d⟩, size := n }
        (.mbarrier ⟨.shared, g / L.block, m⟩) .whole none) (next t) := by
  rw [tmaTmpl_cpBulk_cta]
  simp only [Flow.effAddr_b32 hd hda, effAddr_global hs hsa, Flow.mbarLoc_b32 hm hma hmal,
    readBits_imm hn', bind, Except.bind, Proof.toNat_ofNat_lt (show n < 2 ^ 64 by omega)]
  rw [ite_eq_left ⟨hn, hn16, hd16, hs16⟩, ite_eq_left hr]
  rfl

theorem tma_tryWait {p r : Nat} {a : Nat} (h : t.regs r = some (b32 a)) (ha : a < 2 ^ 32)
    (hal : a % 8 = 0) :
    tmaTmpl L g t (.mbarWait p r 0 (.imm 0)) =
      .wait ⟨.shared, g / L.block, a⟩ 0 (fun ok => next (setReg t p (.pred ok))) := by
  simp only [tmaTmpl, Flow.mbarLoc_b32 h ha hal, bind, Except.bind]
  rfl

end

end PTX.Proof
