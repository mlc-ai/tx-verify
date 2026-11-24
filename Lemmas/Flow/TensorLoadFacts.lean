-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.TensorBox
public import Lemmas.Flow.TensorCoords
public import Lemmas.Flow.Events

@[expose] public section

/-! # The fields of a tensor load's copy

A proof tool. A unicast tensor load that issues a copy
(`fires_cpTensor_copy`: whatever its cache policy, and a firing that may stop the thread) has
the copy `tensorLoadCopy` computes, whose fields follow from its operand registers: the map
parameter its map register names (`tensorMapAddress_param`), the destination a shared pointer
register plus the immediate offset resolves to (`sharedEffAddr_ptr`), and the origin a list of
32-bit coordinate registers holds (`tensorLoadCopy_origin_regs`). -/

namespace PTX.Flow
open PTX PTX.Proof

noncomputable section

/-- The copy a firing tensor load issues is the copy `tensorLoadCopy` computes. -/
theorem fires_cpTensor_copy {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {o : Option TState} {ca grp : Bool} {dst mb : Nat} {off moff : Int} {map : Opnd}
    {cs : List Opnd} {lm : TensorMode} {pol : Option Opnd} {pc : Nat} {e : Event}
    (hf : Fires pc (eventTmpl A L g t (.cpTensor ca grp dst off map cs mb moff none lm pol)) e o)
    {a : Nat} {s : TensorCopy.Spec} (hk : e.kind = .tensorIssue a s) :
    tensorLoadCopy L g t ca grp dst off map cs mb moff lm = .ok (a, s) := by
  have hf' : Fires pc (tensorTmpl L g t (.cpTensor ca grp dst off map cs mb moff none lm pol)) e
      o := hf
  simp only [tensorTmpl, ofExec, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at hf'
  rcases hp : cachePolicyRead L g t pol with f | ⟨⟩ <;> rw [hp] at hf'
  · simp only [Fires] at hf'; rw [hf'.1] at hk; cases hk
  · rcases hc : tensorLoadCopy L g t ca grp dst off map cs mb moff lm with f | ⟨a', s'⟩ <;>
      rw [hc] at hf'
    · simp only [Fires] at hf'; rw [hf'.1] at hk; cases hk
    · dsimp only at hf'
      split_ifs at hf'
      · simp only [Fires] at hf'
        rw [hf'.1] at hk
        cases hk
        rfl
      · simp only [Fires] at hf'; rw [hf'.1] at hk; cases hk

/-- The coordinates of a tensor load's origin are its coordinate operands' low 32 bits. -/
theorem tensorLoadCopy_origin_all {L : Launch} {g : Nat} {t : TState} {ca grp : Bool}
    {dst mb : Nat} {off moff : Int} {map : Opnd} {cs : List Opnd} {lm : TensorMode} {a : Nat}
    {s : TensorCopy.Spec} {vs : List (BitVec 64)}
    (h : tensorLoadCopy L g t ca grp dst off map cs mb moff lm = .ok (a, s))
    (hvs : cs.mapM (readBits L g t 32) = .ok vs) :
    ∀ i : Fin (s.outer + 1), s.origin i = (BitVec.ofNat 32 (vs.getD i.val 0).toNat).toInt := by
  unfold tensorLoadCopy at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
    hvs] at h
  rcases hm : tensorMap L g t map cs lm with f | ⟨a', outer, d⟩ <;> rw [hm] at h
  · cases h
  rcases hd : sharedEffAddr L g t ca dst off with f | dl <;> simp only [hd] at h
  · cases h
  all_goals repeat' (split at h <;> (try (cases h; done)))
  all_goals cases h
  all_goals intro i
  all_goals rfl

/-- The origin of a four-coordinate tensor load whose coordinate registers hold 32-bit values
below `2 ^ 31`: those values. -/
theorem tensorLoadCopy_origin_regs {L : Launch} {g : Nat} {t : TState} {ca grp : Bool}
    {dst mb r0 r1 r2 r3 x0 x1 x2 x3 : Nat} {off moff : Int} {map : Opnd} {lm : TensorMode}
    {a : Nat} {s : TensorCopy.Spec}
    (h : tensorLoadCopy L g t ca grp dst off map [.reg r0, .reg r1, .reg r2, .reg r3] mb moff lm =
      .ok (a, s))
    (h0 : t.regs r0 = some (b32 x0)) (h1 : t.regs r1 = some (b32 x1))
    (h2 : t.regs r2 = some (b32 x2)) (h3 : t.regs r3 = some (b32 x3)) (hx0 : x0 < 2 ^ 31)
    (hx1 : x1 < 2 ^ 31) (hx2 : x2 < 2 ^ 31) (hx3 : x3 < 2 ^ 31) :
    ∀ i : Fin (s.outer + 1), s.origin i = ([x0, x1, x2, x3].getD i.val 0 : Nat) := by
  have hv := tensorLoadCopy_origin_all h (vs := [BitVec.ofNat 64 x0, BitVec.ofNat 64 x1,
    BitVec.ofNat 64 x2, BitVec.ofNat 64 x3]) (by
      simp only [List.mapM_cons, List.mapM_nil, readBits_b32 h0 (by omega),
        readBits_b32 h1 (by omega), readBits_b32 h2 (by omega), readBits_b32 h3 (by omega),
        bind, Except.bind, pure, Except.pure])
  have key : ∀ x : Nat, x < 2 ^ 31 → (BitVec.ofNat 32 (BitVec.ofNat 64 x).toNat).toInt = x := by
    intro x hx
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact toInt_ofNat_lt32 hx
  intro i
  rw [hv i]
  rcases i with ⟨_ | _ | _ | _ | i, hi⟩
  · exact key x0 hx0
  · exact key x1 hx1
  · exact key x2 hx2
  · exact key x3 hx3
  · simp [List.getD]

/-- A tensor map register holding a parameter pointer resolves to that parameter's object. -/
theorem tensorMapAddress_param {L : Launch} {g : Nat} {t : TState} {rm a : Nat} {name : String}
    (hr : t.regs rm = some (.ptr 64 true (.param name) 0))
    (h : tensorMapAddress L g t (.reg rm) = .ok a) :
    ∃ decl, L.paramObjects name = some (decl, a) := by
  simp only [tensorMapAddress, readValue, readReg, hr, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw, true_and] at h
  rcases ho : L.paramObjects name with _ | ⟨decl, base⟩ <;> simp only [ho] at h
  · cases h
  · split_ifs at h <;> (simp only [Except.ok.injEq] at h; subst h; exact ⟨decl, rfl⟩)

/-- A shared pointer register plus an immediate offset, as a cluster address. -/
theorem sharedEffAddr_ptr {L : Launch} {g : Nat} {t : TState} {base cta a o : Nat} {off : Int}
    (hr : t.regs base = some (.ptr 32 false (.shared (g / L.block) cta) (BitVec.ofNat 64 a)))
    (hg : g < L.threads) (hcta : cta < L.grid)
    (hcl : L.clusterOfCta cta = L.clusterOfCta (g / L.block)) (ha : a + o < 2 ^ 32)
    (ho : off = o) :
    sharedEffAddr L g t true base off = .ok ⟨.shared, cta, a + o⟩ := by
  subst ho
  have h64 : a < 2 ^ 64 := by omega
  have hoff : (BitVec.ofNat 64 a).toNat < 2 ^ 32 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]; omega
  have hl := readSharedAddress_ptr (gen := false) (cl := true) hr (.inl rfl) hg hcta hcl
    (.inl rfl) (.inr rfl) hoff
  have hv : (truncBits 32 (BitVec.ofNat 64 a + BitVec.ofInt 64 (o : Int))).toNat = a + o := by
    simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt, BitVec.toNat_add]
    omega
  simp only [sharedEffAddr, readReg, hr, hl, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, bind,
    Except.bind, pure, Except.pure, hv]

end

end PTX.Flow
