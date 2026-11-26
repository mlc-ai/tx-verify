-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Conversion.Interface
public import Kernels.FlashKdaFwd.Proof.Thread.RunPtr
public import Kernels.FlashKdaFwd.Proof.Thread.Sound

@[expose] public section

/-! # Tools for the phases that read the state buffer through swizzled generic pointers

Generic lemmas of the Conversion and CarryLoad phases of the reference layer; nothing here
names a position of a phase (the Epilogue's 128 generic stores can use the pointer part as it
is).

* `phase_inv_from`: the induction of `Ref/Lib.lean: phase_inv` for a phase that a thread
  enters at an event `k0` of its trace (the exit of the phase before) instead of at its first
  state.
* `ldNext`, `ldNext0`: the two forms of the machine's successor at a 32-bit data load (with and
  without a data or pointer run behind the load), and their inversions.
* `reg_x`: an opaque register that is live at a state's site holds the file's slot.
* `gld`, `sst`, `ev_gld`, `ev_sst`, `ev_bar0`, `ev_fence`: the event of a generic `ld.b32`
  through a pointer into the own window (a read of four bytes at the pointer's address, never
  undefined behaviour when the address is a multiple of four), of a `st.shared.b16` (a write
  of two bytes, or undefined behaviour when the source value does not convert), of
  `bar.sync 0` and of `fence.proxy.async.shared::cta`.
* `swzN_eq`: the swizzle on numbers as arithmetic: bit 4 flips when bit 7 is set;
  `swzN_lo`, `swzN_hi`, `swzN_mod4`; `swz_W`: the machine's swizzle of a word is `swzN`.
* `movedBy_W`, `movedOff_W`: a pointer moved by a word or a constant, on numbers.
* `cvta_shared`, `word_run`, `const_run`: the three kinds of pointer code of these phases,
  evaluated on the pointer `sptr g a` (the generic pointer to address `a` of the thread's own
  window): `cvta.shared.u64` of the shared base; "move by a word, move by 32768, swizzle"; "move
  by a constant, swizzle". Each gives the run's condition (the thread is alive) and the
  pointer it leaves, `sptr g (swzN …)`. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Conversion
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}
  {t : TState} {e : Event} {o : Option TState} {d' : D}

/-! ### The induction of a phase that starts inside a trace -/

/-- **A phase invariant along a thread's states, from the entry of the phase.** The state
before the thread's event `k0` satisfies `I`; each step from a state with `I` leads to a state
with `I` or with the exit condition `E`. Then `I` holds before every later event until `E` held
at an earlier position. -/
theorem phase_inv_from {K : Kernel} {A : List Assumption} {C : (g : Nat) → Flow.Code K A L g}
    (hC : ∀ g < L.threads, (C g).Sound) (hX : Consistent L K A mem0 X) {k0 : Nat}
    {s0 : (C g).D} (hσ0 : Frame.stateAt C X g k0 = some (some s0))
    (I E : Nat → (C g).D → Prop) (h0 : I k0 s0)
    (hs : ∀ (k : Nat) (e : Event) (s s' : (C g).D) (t : TState) (ins : Instr)
      (o : Option TState), k0 ≤ k → X.get (g, k) = some e →
      Frame.stateAt C X g k = some (some s) →
      I k s → (C g).AtD s t → K.code[(C g).pc s]? = some ins →
      Fires ((C g).pc s) (eventTmpl A L g t ins.op) e o → (∀ pc f, e ≠ ⟨pc, .ub f⟩) →
      (C g).next s e = some (some s') → I (k + 1) s' ∨ E (k + 1) s') :
    ∀ k s, k0 ≤ k → k < (X.tr g).length → Frame.stateAt C X g k = some (some s) →
      I k s ∨ ∃ j, k0 ≤ j ∧ j ≤ k ∧ ∃ s1, Frame.stateAt C X g j = some (some s1) ∧ E j s1 := by
  have key := phase_inv (C := C) hC hX (fun k s => k0 ≤ k → I k s)
    (fun k s => k0 ≤ k ∧ E k s) (by
      intro h
      obtain rfl : k0 = 0 := by omega
      rw [Frame.stateAt_zero] at hσ0
      cases hσ0
      exact h0) (by
      intro k e s s' t ins o he hσ hI hat hc hf hub hn
      by_cases hk : k0 ≤ k
      · rcases hs k e s s' t ins o hk he hσ (hI hk) hat hc hf hub hn with h | h
        · exact .inl fun _ => h
        · exact .inr ⟨by omega, h⟩
      · refine .inl fun hk1 => ?_
        obtain rfl : k0 = k + 1 := by omega
        rw [Frame.stateAt_succ he, hσ] at hσ0
        have : s' = s0 := Option.some.inj (Option.some.inj (hn.symm.trans hσ0))
        rw [this]
        exact h0)
  intro k s hk0 hk hσ
  rcases key k s hk hσ with h | ⟨j, hj, s1, h1, h2, h3⟩
  · exact .inl (h hk0)
  · exact .inr ⟨j, h2, hj, s1, h1, h3⟩

/-! ### The successor at a 32-bit data load -/

/-- **The successor at a 32-bit load that a run follows**: the event is a read whose four
bytes have a value `v` (`ldVal`), the run behind the load continues under its condition
`c v`, and the next state is `f v`; otherwise the thread is dead. -/
def ldNext (e : Event) (c : Value → Prop) (f : Value → D) : Option (Option D) :=
  match e.kind with
  | .rd _ bs =>
    match ldVal .same 32 bs with
    | .ok v => across (c v) (f v)
    | .error _ => none
  | _ => none

/-- The successor at a 32-bit load with no run behind it. -/
def ldNext0 (e : Event) (f : Value → D) : Option (Option D) :=
  match e.kind with
  | .rd _ bs =>
    match ldVal .same 32 bs with
    | .ok v => some (some (f v))
    | .error _ => none
  | _ => none

theorem across_some {D : Type} {c : Prop} {d d' : D} (h : across c d = some (some d')) :
    c ∧ d' = d := by
  by_cases hc : c
  · rw [across_pos hc] at h
    exact ⟨hc, (Option.some.inj (Option.some.inj h)).symm⟩
  · rw [across_neg hc] at h
    cases h

theorem under_some {D : Type} {c : Prop} {o : Option (Option D)} {d' : D}
    (h : under c o = some (some d')) : c ∧ o = some (some d') := by
  by_cases hc : c
  · rw [under_pos hc] at h
    exact ⟨hc, h⟩
  · rw [under_neg hc] at h
    cases h

theorem ldNext_some {c : Value → Prop} {f : Value → D} (h : ldNext e c f = some (some d')) :
    ∃ a bs v, e.kind = .rd a bs ∧ ldVal .same 32 bs = .ok v ∧ c v ∧ d' = f v := by
  unfold ldNext at h
  split at h
  · rename_i a bs hk
    split at h
    · rename_i v hv
      obtain ⟨hc, rfl⟩ := across_some h
      exact ⟨a, bs, v, hk, hv, hc, rfl⟩
    · cases h
  · cases h

theorem ldNext_ok {c : Value → Prop} {f : Value → D} {a : Acc} {bs : List (Option Byte)}
    {v : Value} (hk : e.kind = .rd a bs) (hv : ldVal .same 32 bs = .ok v) (hc : c v) :
    ldNext e c f = some (some (f v)) := by
  obtain ⟨pc, k⟩ := e
  simp only at hk
  subst hk
  simp only [ldNext, hv, across_pos hc]

theorem ldNext0_some {f : Value → D} (h : ldNext0 e f = some (some d')) :
    ∃ a bs v, e.kind = .rd a bs ∧ ldVal .same 32 bs = .ok v ∧ d' = f v := by
  unfold ldNext0 at h
  split at h
  · rename_i a bs hk
    split at h
    · rename_i v hv
      exact ⟨a, bs, v, hk, hv, (Option.some.inj (Option.some.inj h)).symm⟩
    · cases h
  · cases h

theorem ldNext0_ok {f : Value → D} {a : Acc} {bs : List (Option Byte)} {v : Value}
    (hk : e.kind = .rd a bs) (hv : ldVal .same 32 bs = .ok v) :
    ldNext0 e f = some (some (f v)) := by
  obtain ⟨pc, k⟩ := e
  simp only at hk
  subst hk
  simp only [ldNext0, hv]

/-! ### Registers of a concrete state -/

/-- An opaque register that is live at a state's site holds the file's slot. -/
theorem reg_x {d : D} {t : TState} (hat : (code L g).AtD d t) {r : Nat}
    (hr : r ∈ Flow.live d.site.pc) (hk : isOpaque r = true) : t.regs r = some (d.x r) := by
  have h := regs_of_factsFrom hat.2.2.2.2 hr
  rw [h, valueOf_opaque hk]

/-- A launched thread's block is in the grid. -/
theorem grid_of (hpre : Pre P L mem0) (hg : g < L.threads) : g / L.block < L.grid := by
  have := cta_lt_nclusters hpre hg
  rwa [hpre.nclusters] at this

/-! ### Events -/

/-- The generic load `ld.b32 d, [r]` through the 64-bit pointer register `r`. -/
def gld (r d : Nat) : MemAccess :=
  { kind := .load, space := none, sem := .weak, scope := none, elem := .int .b 32, vec := 1,
    ext := .same, nc := false, noftz := false,
    hints := { cop := none, l1 := none, l2 := none, prefetch := none, policy := none },
    addr := { base := .reg r 64, off := 0 }, dsts := [some d], srcs := [], mmio := false }

/-- The store `st.shared.b16 [r], s` through the 32-bit address register `r`. -/
def sst (r s : Nat) : MemAccess :=
  { kind := .store, space := some (.shared .cta), sem := .weak, scope := none,
    elem := .int .b 16, vec := 1, ext := .same, nc := false, noftz := false,
    hints := { cop := none, l1 := none, l2 := none, prefetch := none, policy := none },
    addr := { base := .reg r 32, off := 0 }, dsts := [], srcs := [.reg s], mmio := false }

/-- The footprint of a generic `ld.b32` through a generic pointer into the thread's own
shared window, at a multiple of four. -/
theorem accessAcc_gld {r d : Nat} {off : BitVec 64}
    (hr : t.regs r = some (.ptr 64 true (.shared (g / L.block) (g / L.block)) off))
    (hg : g < L.threads) (hc : g / L.block < L.grid) (ho : off.toNat < 2 ^ 32)
    (hal : off.toNat % 4 = 0) (hs : t.sub = 0) :
    accessAcc L g t (gld r d) =
      .ok { loc := ⟨.shared, g / L.block, off.toNat⟩, size := 4 } := by
  have ho' : off.toNat < 4294967296 := ho
  simp [accessAcc, accessLoc, gld, readReg, hr, readSharedAddress, readValue, hg, hc, ho', hal,
    hs, elemAcc, MemAccess.semAcc, MemAccess.strongLocOk, bind, Except.bind, pure, Except.pure,
    DType.width, Loc.at]

/-- **The event of a generic `ld.b32` through a pointer to address `a` of the own window**: a
read of the four bytes at `a`; it is not undefined behaviour. -/
theorem ev_gld (hpre : Pre P L mem0) (hg : g < L.threads) {pc r d a : Nat}
    (hf : Fires pc (eventTmpl Assumptions.all L g t (.mem (gld r d))) e o)
    (hr : t.regs r = some (sptr g a)) (ha : a < 2 ^ 32) (hal : a % 4 = 0) (hs : t.sub = 0) :
    ∃ bs, bs.length = 4 ∧ e = ⟨pc, .rd { loc := ⟨.shared, cta g, a⟩, size := 4 } bs⟩ := by
  have hw : (W a).toNat = a := toNat_W (by omega)
  rw [sptr, ← block_div hpre] at hr
  have hacc := accessAcc_gld (d := d) hr hg (grid_of hpre hg) (by rw [hw]; exact ha)
    (by rw [hw]; exact hal) hs
  rw [hw, block_div hpre] at hacc
  exact shape_accessLd (P := fun e' => ∃ bs, bs.length = 4 ∧
    e' = ⟨pc, .rd { loc := ⟨.shared, cta g, a⟩, size := 4 } bs⟩) hf rfl rfl rfl hacc
    fun bs hbs => ⟨bs, hbs, rfl⟩

/-- **The event of a `st.shared.b16` to address `a` of the own window** from a register that
holds `v`: a write of the two bytes of the converted value (`storeValue`), or undefined
behaviour when the value does not convert. -/
theorem ev_sst (hpre : Pre P L mem0) {pc r s a : Nat} {v : Value}
    (hf : Fires pc (eventTmpl Assumptions.all L g t (.mem (sst r s))) e o)
    (hr : t.regs r = some (.bits 32 (W a))) (hv : t.regs s = some v) (ha : a < 2 ^ 32)
    (hal : a % 2 = 0) (hs : t.sub = 0) :
    (∃ v', storeValue 16 v = .ok v' ∧
      e = ⟨pc, .wr { loc := ⟨.shared, cta g, a⟩, size := 2 } v'.toBytes⟩) ∨
    (∃ f, storeValue 16 v = .error f ∧ e = ⟨pc, .ub f⟩) := by
  have hE : eventTmpl Assumptions.all L g t (.mem (sst r s)) =
      storeTmpl L g t .shared 16 r 0 [.reg s] := rfl
  rw [hE] at hf
  have hea := effAddr_shared32 (L := L) (g := g) (off := 0) hr
  have hl : (truncBits 32 (truncBits 32 (W a) + BitVec.ofInt 64 0)).toNat = a := by
    simp only [truncBits, W, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
    omega
  rw [hl, block_div hpre] at hea
  refine shape_stM (P := fun e' => (∃ v', storeValue 16 v = .ok v' ∧
      e' = ⟨pc, .wr { loc := ⟨.shared, cta g, a⟩, size := 2 } v'.toBytes⟩) ∨
    (∃ f, storeValue 16 v = .error f ∧ e' = ⟨pc, .ub f⟩)) hf hea hs rfl
    (by simp only [readValue, readReg, hv]; rfl) (fun v' hv' => .inl ⟨v', hv', rfl⟩)
    (fun hm => ?_) (fun f hf' => .inr ⟨f, hf', rfl⟩)
  exfalso
  simp at hm
  omega

/-- The event of `bar.sync 0`. -/
theorem ev_bar0 {pc : Nat}
    (hf : Fires pc (eventTmpl Assumptions.all L g t (.barSync (.imm 0) true)) e o) :
    e = ⟨pc, .bar 0 none .sync⟩ :=
  shape_barSync (P := fun e' => e' = ⟨pc, .bar 0 none .sync⟩) hf (by decide) rfl

/-- The event of `fence.proxy.async.shared::cta`. -/
theorem ev_fence {pc : Nat}
    (hf : Fires pc (eventTmpl Assumptions.all L g t
      (.fence (.proxy (.async (some (.shared .cta))) none none))) e o) :
    e = ⟨pc, .fenceProxy (.async (some (.shared .cta))) none⟩ :=
  shape_fenceProxy
    (P := fun e' => e' = ⟨pc, .fenceProxy (.async (some (.shared .cta))) none⟩) hf rfl

/-! ### The swizzle on numbers -/

theorem and16_eq (m : Nat) : m &&& 16 = 16 * (m / 16 % 2) := by
  have h1 : (m &&& 16) / 2 ^ 5 = 0 := by
    rw [Nat.and_div_two_pow]
    simp
  have h2 : (m &&& 16) % 2 ^ 5 = (m % 2 ^ 5) &&& (16 % 2 ^ 5) := Nat.and_mod_two_pow
  have h3 : ∀ b < 32, b &&& 16 = 16 * (b / 16 % 2) := by decide
  have h4 := h3 (m % 32) (Nat.mod_lt _ (by decide))
  norm_num at h1 h2
  omega

theorem xor16_eq (n : Nat) : n ^^^ 16 = if n / 16 % 2 = 1 then n - 16 else n + 16 := by
  have h1 : (n ^^^ 16) / 2 ^ 5 = n / 2 ^ 5 ^^^ 16 / 2 ^ 5 := Nat.xor_div_two_pow
  have h2 : (n ^^^ 16) % 2 ^ 5 = n % 2 ^ 5 ^^^ 16 % 2 ^ 5 := Nat.xor_mod_two_pow
  have h3 : ∀ b < 32, b ^^^ 16 = if b / 16 % 2 = 1 then b - 16 else b + 16 := by decide
  have h4 := h3 (n % 32) (Nat.mod_lt _ (by decide))
  norm_num at h1 h2
  split_ifs at h4 ⊢ <;> omega

/-- **The swizzle as arithmetic**: when bit 7 of the address is set, bit 4 is flipped. -/
theorem swzN_eq (n : Nat) :
    swzN n = if n / 128 % 2 = 1 then (if n / 16 % 2 = 1 then n - 16 else n + 16) else n := by
  unfold swzN
  rw [Nat.shiftRight_eq_div_pow, and16_eq]
  have e : n / 2 ^ 3 / 16 % 2 = n / 128 % 2 := by omega
  rw [e]
  by_cases h : n / 128 % 2 = 1
  · simp only [h, ↓reduceIte, Nat.mul_one]
    exact xor16_eq n
  · have h0 : n / 128 % 2 = 0 := by omega
    simp [h0]

/-- The swizzle stays in the 32-byte row of the address. -/
theorem swzN_row (n : Nat) : swzN n / 32 = n / 32 ∧ swzN n % 16 = n % 16 := by
  rw [swzN_eq]
  split_ifs <;> omega

/-- The swizzle of an address of a 128-byte-aligned region stays in the region. -/
theorem swzN_lo {n b : Nat} (hb : b % 32 = 0) (h : b ≤ n) : b ≤ swzN n := by
  have := swzN_row n
  omega

theorem swzN_hi {n b : Nat} (hb : b % 32 = 0) (hn : n % 4 = 0) (h : n < b) :
    swzN n + 4 ≤ b := by
  have := swzN_row n
  omega

theorem swzN_mod4 {n : Nat} (hn : n % 4 = 0) : swzN n % 4 = 0 := by
  have := swzN_row n
  omega

theorem swzN_lt {n : Nat} (hn : n + 16 < 2 ^ 32) : swzN n < 2 ^ 32 := by
  rw [swzN_eq]
  split_ifs <;> omega

/-- **The machine's swizzle of a word is the swizzle of its number.** -/
theorem swz_W {n : Nat} (h : n < 2 ^ 32) : Rules.swz (W n) = W (swzN n) := by
  have hs : swzN n < 2 ^ 64 := by
    rw [swzN_eq]
    split_ifs <;> omega
  apply BitVec.eq_of_toNat_eq
  rw [toNat_W hs]
  simp only [Rules.swz, swzN, BitVec.toNat_xor, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    toNat_W (show n < 2 ^ 64 by omega), BitVec.toNat_ofNat]

/-! ### Pointer moves on numbers -/

theorem W_ofInt (b : Nat) : W b = BitVec.ofInt 64 (b : Int) := (Rules.ofInt_natCast b).symm

/-- **A pointer at `a` moved by the word `b`** is at `a + b`, when that is in the window. -/
theorem movedBy_W {a b : Nat} (hb : b < 2 ^ 63) (h : a + b < 2 ^ 32) :
    Rules.movedBy (W a) (W b) = W (a + b) ∧ Rules.MoveOkW (W a) (W b) := by
  have h1 := Rules.movedOff_nat (off := W a) (k := b) hb (by
    rw [toNat_W (by omega)]; exact h)
  rw [toNat_W (show a < 2 ^ 64 by omega)] at h1
  rw [W_ofInt b]
  exact h1

/-- **A pointer at `a` moved by the constant `k`** is at `a + k`, when that is in the
window. -/
theorem movedOff_W {a : Nat} (k : Nat) (hk : k < 2 ^ 63) (h : a + k < 2 ^ 32) :
    Rules.movedOff (W a) (k : Int) = W (a + k) ∧ Rules.MoveOk (W a) (k : Int) := by
  have h1 := Rules.movedOff_nat (off := W a) (k := k) hk (by
    rw [toNat_W (by omega)]; exact h)
  rwa [toNat_W (show a < 2 ^ 64 by omega)] at h1

/-! ### The pointer code of the two phases, on `sptr` -/

/-- **`cvta.shared.u64` of the shared base** (a 64-bit word register `r` that holds the
address `a` of the window): for a launched thread the conversion's condition holds and it
writes the pointer `sptr g a`. -/
theorem cvta_shared (hpre : Pre P L mem0) (hg : g < L.threads) {V : Nat → Value} {r a : Nat}
    (hV : V r = .bits 64 (W a)) (ha : a < 2 ^ 32) :
    Rules.cvtaCond L g V r ∧ Rules.cvtaVal L g V r = sptr g a := by
  have ht : (truncBits 64 (W a)).toNat = a := by
    rw [Rules.truncBits_64, toNat_W (by omega)]
  have h := Rules.cvta_eval (L := L) (g := g) hV hg (grid_of hpre hg) (by rw [ht]; exact ha)
  rw [ht, block_div hpre] at h
  exact h

/-- **A pointer run "move by a word, move by 32768, swizzle"** (`hrun`: its lemma of
`Thread/RunPtr.lean`) from the base pointer `sptr g a` and the word `b`: the run's condition
holds and it leaves the pointer to the swizzled address of `a + b + 32768`. -/
theorem word_run {cond : (Nat → Value) → Prop} {facts : (Nat → Value) → List (Nat × Value)}
    {rb rw ro : Nat} {V : Nat → Value}
    (hrun : ∀ {o c : Nat} {off delta : BitVec 64} {n : Nat},
      V rb = .ptr 64 true (.shared o c) off → V rw = .bits n delta →
      Rules.MoveOkW off delta → Rules.MoveOk (Rules.movedBy off delta) 32768 →
      cond V ∧ facts V = [(ro, .ptr 64 true (.shared o c)
        (Rules.swz (Rules.movedOff (Rules.movedBy off delta) 32768)))])
    {a b : Nat} (hb : V rb = sptr g a) (hw : V rw = .bits 64 (W b))
    (hab : a + b + 32768 < 2 ^ 32) :
    cond V ∧ facts V = [(ro, sptr g (swzN (a + b + 32768)))] := by
  obtain ⟨e1, m1⟩ := movedBy_W (a := a) (b := b) (by omega) (by omega)
  obtain ⟨e2, m2⟩ := movedOff_W (a := a + b) 32768 (by norm_num) hab
  have h := hrun hb hw m1 (by rw [e1]; exact m2)
  rw [e1] at h
  have e3 : Rules.movedOff (W (a + b)) 32768 = W (a + b + 32768) := e2
  rw [e3, swz_W hab] at h
  exact h

/-- **A pointer run "move by the constant `k`, swizzle"** from the base pointer `sptr g a`:
the run's condition holds and it leaves the pointer to the swizzled address of `a + k`. -/
theorem const_run {cond : (Nat → Value) → Prop} {facts : (Nat → Value) → List (Nat × Value)}
    {rb ro : Nat} {V : Nat → Value} (k : Nat)
    (hrun : ∀ {o c : Nat} {off : BitVec 64},
      V rb = .ptr 64 true (.shared o c) off → Rules.MoveOk off (k : Int) →
      cond V ∧ facts V = [(ro, .ptr 64 true (.shared o c)
        (Rules.swz (Rules.movedOff off (k : Int))))])
    {a : Nat} (hb : V rb = sptr g a) (hak : a + k < 2 ^ 32) :
    cond V ∧ facts V = [(ro, sptr g (swzN (a + k)))] := by
  obtain ⟨e2, m2⟩ := movedOff_W (a := a) k (by omega) hak
  have h := hrun hb m2
  rw [e2, swz_W hak] at h
  exact h

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Conversion
