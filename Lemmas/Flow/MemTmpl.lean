-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Bits

@[expose] public section

/-!
# Memory instructions

The event templates of scalar global loads and stores, from register facts: the footprint
is `⟨.global, 0, a⟩` for a base register holding `a`, aligned.
-/

namespace PTX.Proof
open PTX

section
variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState}

theorem out_event {K : Kernel} {ins : Instr} (hf : t.fault = none) (hc : K.code[t.pc]? = some ins)
    (hgd : guardHolds t ins.guard = .ok true) (hl : ins.op.isLocal = false) :
    out K A L g t = .ev (eventTmpl A L g t ins.op) := by
  unfold out; rw [hf]; simp only [hc, hgd, hl, Bool.false_eq_true, ↓reduceIte]

theorem execLocalA_nil {op : Op} : execLocalA [] L g t op = execLocal L g t op := by
  unfold execLocalA execLocalRule
  simp only [List.findSome?_nil]

/-- A local instruction that succeeds is a local step. -/
theorem out_tau {K : Kernel} {ins : Instr} {t' : TState} (hf : t.fault = none)
    (hc : K.code[t.pc]? = some ins) (hgd : guardHolds t ins.guard = .ok true)
    (hl : ins.op.isLocal = true) (he : execLocalA A L g t ins.op = .ok t') :
    out K A L g t = .tau t' := by
  unfold out; rw [hf]; simp only [hc, hgd, hl, ↓reduceIte, he]

/-- A local instruction that fails performs undefined behaviour. -/
theorem out_ub {K : Kernel} {ins : Instr} {f : Fault} (hf : t.fault = none)
    (hc : K.code[t.pc]? = some ins) (hgd : guardHolds t ins.guard = .ok true)
    (hl : ins.op.isLocal = true) (he : execLocalA A L g t ins.op = .error f) :
    out K A L g t = .ev (.ub f) := by
  unfold out; rw [hf]; simp only [hc, hgd, hl, ↓reduceIte, he]

theorem effAddr_global {r : Nat} {a : Nat} (h : t.regs r = some (b64 a)) (ha : a < 2 ^ 64) :
    effAddr L g t .global r 0 = .ok ⟨.global, 0, a⟩ := by
  have : a < 18446744073709551616 := by simpa using ha
  simp [effAddr, readBits, readReg, h, b64, truncBits, bind, Except.bind, pure, Except.pure,
    Nat.mod_eq_of_lt this]

theorem elemAcc_ok {loc : Loc} {n count j : Nat} (hn : 0 < n) (hal : loc.addr % (n * count) = 0) :
    elemAcc loc n count j = .ok { loc := loc.at (n * j), size := n, elem := j } := by
  unfold elemAcc; rw [ite_eq_right (by omega)]; rfl

theorem loadTmpl_global {d base : Nat} {w a : Nat} (hs : t.sub = 0)
    (h : t.regs base = some (b64 a)) (ha : a < 2 ^ 64) (hw : 0 < w / 8) (hal : a % (w / 8) = 0) :
    loadTmpl A L g t .global false w [d] base 0 =
      .read { loc := ⟨.global, 0, a⟩, size := w / 8 } (afterLoad t [d]) := by
  unfold loadTmpl
  rw [effAddr_global h ha]
  simp only [bind, Except.bind, List.length_singleton, hs]
  rw [elemAcc_ok hw (by simpa using hal)]
  simp [Loc.at, Bool.false_eq_true, ↓reduceIte]

theorem loadTmpl_global_nc {d base : Nat} {w a : Nat} (hs : t.sub = 0)
    (h : t.regs base = some (b64 a)) (ha : a < 2 ^ 64) (hw : 0 < w / 8) (hal : a % (w / 8) = 0)
    (hnc : A.any (·.ncLoads t.pc) = true) :
    loadTmpl A L g t .global true w [d] base 0 =
      .readNC { loc := ⟨.global, 0, a⟩, size := w / 8 } (afterLoad t [d]) := by
  unfold loadTmpl
  rw [effAddr_global h ha]
  simp only [bind, Except.bind, List.length_singleton, hs]
  rw [elemAcc_ok hw (by simpa using hal)]
  simp [Loc.at, hnc]

/-- A store of a register to global memory writes the value read at the store's width after
`storeValue`: a source of the store's own size unchanged, a wider source truncated to the store's
bytes. -/
theorem storeTmpl_global {base src : Nat} {w a : Nat} {v : Value} (hs : t.sub = 0)
    (h : t.regs base = some (b64 a)) (ha : a < 2 ^ 64) (hw : 0 < w / 8) (hal : a % (w / 8) = 0)
    (hv : t.regs src = some v) :
    storeTmpl L g t .global w base 0 [.reg src] =
      match storeValue w v with
      | .error f => .ub f
      | .ok v' => .write { loc := ⟨.global, 0, a⟩, size := w / 8 } v'.toBytes
        (afterStore t [.reg src]) := by
  unfold storeTmpl
  rw [effAddr_global h ha]
  simp only [bind, Except.bind, List.length_singleton, hs]
  rw [elemAcc_ok hw (by simpa using hal)]
  simp [Loc.at, readValue, readReg, hv, pure, Except.pure]
  cases storeValue w v <;> rfl

/-- After a scalar load whose bytes rebuild to `v`. -/
theorem afterLoad_ok {d : Nat} {bs : List (Option Byte)} {v : Value} (hs : t.sub = 0)
    (hacc : t.acc = []) (hv : rebuild 3 bs = .ok v) :
    afterLoad t [d] bs = { setReg t d v with pc := t.pc + 1, sub := 0, acc := [] } := by
  simp [afterLoad, hv, hs, hacc, setRegs]

/-- The bytes of one stored scalar read back give that scalar. -/
theorem rebuild_scalar {v : Value} (hv : 0 < v.bytes) (hs : v.byteAt 0 = (v, 0)) :
    rebuild 3 (v.toBytes.map some) = .ok v := by
  obtain ⟨n, hn⟩ : ∃ n, v.bytes = n + 1 := ⟨v.bytes - 1, by omega⟩
  have e : v.toBytes.map some =
      some (v, 0) :: (List.range n).map (fun k => some (v.byteAt (k + 1))) := by
    simp [Value.toBytes, hn, List.range_succ_eq_map, hs]
  rw [e]
  simp only [rebuild]
  rw [ite_eq_left ⟨by simp [hn], e.symm⟩]
  rfl

/-- The bits of read bytes are as long as the bytes. -/
theorem rebuildBits_bytes {bs : List (Option Byte)} {w : Value} (h : rebuildBits bs = some w) :
    w.bytes = bs.length := by
  unfold rebuildBits at h
  split at h
  · rename_i h1
    cases hx : littleEndianBits bs with
    | none => simp [hx] at h
    | some x =>
      simp only [hx, bind, Option.bind, pure, Option.some.injEq] at h
      subst h
      rcases h1 with h1 | h1 | h1 | h1 <;> simp [Value.bytes, h1]
  · split at h
    · rename_i h1
      cases hx : littleEndianBits bs with
      | none => simp [hx] at h
      | some x =>
        simp only [hx, bind, Option.bind, pure] at h
        simp only [Option.some.injEq] at h
        subst h
        simp [Value.bytes, h1]
    · simp at h

private theorem halves_ok_bytes {f : Nat} {bs : List (Option Byte)} {v : Value}
    (h : rebuild.halves f bs = .ok v)
    (ih : ∀ (cs : List (Option Byte)) (w : Value), rebuild f cs = .ok w → w.bytes = cs.length) :
    v.bytes = bs.length := by
  unfold rebuild.halves at h
  split at h
  · simp at h
  · split at h
    · cases hb : rebuildBits bs with
      | none => simp [hb] at h
      | some w =>
        simp only [hb] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact rebuildBits_bytes hb
    · simp only [bind, Except.bind] at h
      split at h
      · simp at h
      · rename_i lo hlo
        split at h
        · simp at h
        · rename_i hi hhi
          simp only [pure, Except.pure] at h
          rw [Except.ok.injEq] at h
          subst h
          have h1 : lo.bytes = (bs.take (bs.length / 2)).length := ih _ _ hlo
          have h2 : hi.bytes = (bs.drop (bs.length / 2)).length := ih _ _ hhi
          have h3 := List.length_take (l := bs) (i := bs.length / 2)
          have h4 := List.length_drop (l := bs) (i := bs.length / 2)
          simp only [Value.bytes]
          omega

/-- A `rebuild` of `bs` yields a value of `bs.length` bytes. -/
theorem rebuild_bytes_eq_length : ∀ (f : Nat) (bs : List (Option Byte)) (v : Value),
    rebuild f bs = .ok v → v.bytes = bs.length
  | 0, bs, v, h => by simp [rebuild] at h
  | f + 1, bs, v, h => by
    have ih : ∀ (cs : List (Option Byte)) (w : Value), rebuild f cs = .ok w → w.bytes = cs.length :=
      fun cs w hw => rebuild_bytes_eq_length f cs w hw
    cases bs with
    | nil => simp only [rebuild] at h; exact halves_ok_bytes h ih
    | cons b rest =>
      cases b with
      | none => simp only [rebuild] at h; exact halves_ok_bytes h ih
      | some p =>
        obtain ⟨val, k⟩ := p
        cases k with
        | zero =>
          simp only [rebuild] at h
          split at h
          · rename_i hc
            simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            exact hc.1
          · exact halves_ok_bytes h ih
        | succ k => simp only [rebuild] at h; exact halves_ok_bytes h ih

/-- A four-byte `rebuild` yields a four-byte value, so a `b32` load cannot be the source of a
narrower store. -/
theorem rebuild_bytes_of_length {bs : List (Option Byte)} {v : Value}
    (h : rebuild 3 bs = .ok v) (hl : bs.length = 4) : v.bytes = 4 := by
  rw [rebuild_bytes_eq_length 3 bs v h, hl]

end

end PTX.Proof
