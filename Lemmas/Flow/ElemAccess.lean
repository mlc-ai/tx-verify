-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.LoadShared

@[expose] public section

/-! # The footprints of loads and vector stores

A proof tool. A weak load of width `w` reads `w / 8` bytes (`fires_ld_size`). Element `t.sub` of a
32-bit vector store to a shared address held in a register plus an offset writes four bytes at
that address plus the offset plus `4 t.sub`, the bytes of the value its source register holds when
that value has the store's width (`fires_stv32_off`). A `tcgen05.st` without `.unpack::16b`
stores one value per source (`fires_tcSt_len`), the value its register holds (`fires_tcSt_vals`). -/

namespace PTX.Flow
open PTX PTX.Proof

/-- An element access has the element's size. -/
theorem elemAcc_size {base : Loc} {n count j : Nat} {a : Acc} (h : elemAcc base n count j = .ok a) :
    a.size = n := by
  unfold elemAcc at h
  split_ifs at h
  cases h
  rfl

/-- **A load of width `w` reads `w / 8` bytes.** The access is a weak load that THREAD-ACCESS
accepts, at a global or shared location through a register. -/
theorem fires_ld_size {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {pc : Nat}
    {e : Event} {o : Option TState} {a : MemAccess} {sp : Space} {base bw : Nat} {ac : Acc}
    {bs : List (Option Byte)} (hf : Fires pc (eventTmpl A L g t (.mem a)) e o)
    (hk : e.kind = .rd ac bs) (hr : a.rule = some .threadAccess := by rfl)
    (hs : a.locSpace? = some sp := by rfl) (hb : a.addr.base = .reg base bw := by rfl)
    (hl : a.kind = .load := by rfl) (hnc : a.nc = false := by rfl)
    (hsem : a.sem = .weak := by rfl) : ac.size = a.elem.width / 8 := by
  rw [eventTmpl, memTmpl_load hr hs hb hl hsem] at hf
  simp only [loadTmpl, hnc] at hf
  cases h : (effAddr L g t sp base a.addr.off >>= fun loc =>
      elemAcc loc (a.elem.width / 8) a.regs.length t.sub) with
  | error f =>
    rw [h] at hf
    simp only [Fires] at hf
    rw [hf.1] at hk
    cases hk
  | ok a' =>
    rw [h] at hf
    simp only [Bool.false_eq_true, ↓reduceIte, Fires] at hf
    obtain ⟨bs', -, he, -⟩ := hf
    rw [he] at hk
    injection hk with h1
    subst h1
    cases ha : effAddr L g t sp base a.addr.off with
    | error f => rw [ha] at h; cases h
    | ok loc =>
      rw [ha] at h
      exact elemAcc_size h

/-- **Element `t.sub` of a 32-bit shared vector store at an offset**: its footprint and bytes. -/
theorem fires_stv32_off {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {pc : Nat}
    {e : Event} {o : Option TState} {base a n : Nat} {off : Int} {srcs : List Opnd}
    {ik : IType} (hr : t.regs base = some (b32 a)) (hoff : off = (n : Int))
    (ha : a + n < 2 ^ 32) (hn : srcs.length = 1 ∨ srcs.length = 2 ∨ srcs.length = 4)
    (hf : Fires pc (eventTmpl A L g t (.mem
      { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int ik 32,
        vec := srcs.length, addr := ⟨.reg base 32, off⟩, srcs := srcs })) e o) :
    ∀ acc bs, e.kind = .wr acc bs →
      acc.loc = ⟨.shared, g / L.block, a + n + 4 * t.sub⟩ ∧ acc.size = 4 ∧
        ∀ r v, srcs[t.sub]? = some (.reg r) → t.regs r = some v → v.bytes = 32 / 8 →
          bs = v.toBytes := by
  subst hoff
  intro acc bs hk
  have hrule : MemAccess.rule { kind := .store, space := some (.shared .cta), sem := .weak,
                                elem := .int ik 32, vec := srcs.length,
                                addr := ⟨.reg base 32, (n : Int)⟩, srcs := srcs } =
      some .threadAccess := by
    rcases hn with h | h | h <;> cases ik <;> simp [MemAccess.rule,
      memTypeOk, DType.width, h]
  rw [eventTmpl, memTmpl_store (sp := .shared) (base := base) (w := 32) hrule rfl rfl rfl
    (by simp)] at hf
  simp only [DType.width, storeTmpl, effAddr_b32_off hr ha, bind, Except.bind] at hf
  cases hea : elemAcc ⟨.shared, g / L.block, a + n⟩ (32 / 8) srcs.length t.sub with
  | error f =>
    simp only [hea, Fires] at hf
    rw [hf.1] at hk
    cases hk
  | ok a' =>
    simp only [hea] at hf
    have hloc : a'.loc = ⟨.shared, g / L.block, a + n + 4 * t.sub⟩ ∧ a'.size = 4 := by
      unfold elemAcc at hea
      split_ifs at hea
      all_goals simp only [pure, Except.pure, Except.ok.injEq] at hea
      all_goals subst hea
      all_goals exact ⟨by simp [Loc.at], rfl⟩
    cases hs : srcs[t.sub]? with
    | none =>
      simp only [hs, Fires] at hf
      rw [hf.1] at hk
      cases hk
    | some op =>
      simp only [hs] at hf
      cases hv : readValue L g t 32 op with
      | error f =>
        simp only [hv, Fires] at hf
        rw [hf.1] at hk
        cases hk
      | ok v =>
        cases hsv : storeValue 32 v with
        | error f =>
          simp only [hv, hsv, Fires] at hf
          rw [hf.1] at hk
          cases hk
        | ok v' =>
          simp only [hv, hsv, Fires] at hf
          rw [hf.1] at hk
          injection hk with h1 h2
          subst h1 h2
          refine ⟨hloc.1, hloc.2, fun r v'' hr' hv' hb4 => ?_⟩
          obtain rfl : op = .reg r := Option.some.inj hr'
          simp only [readValue, readReg, hv', pure, Except.pure, Except.ok.injEq] at hv
          subst hv
          simp only [storeValue, hb4, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at hsv
          rw [hsv]

/-- A successful `mapM` in `Except` returns one result per element. -/
theorem mapM_except_length {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r → r.length = l.length
  | [], r, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | a :: l, r, h => by
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    cases hb : f a with
    | error e => rw [hb] at h; cases h
    | ok b =>
      rw [hb] at h
      cases hl : l.mapM f with
      | error e => rw [hl] at h; cases h
      | ok bs =>
        rw [hl] at h
        simp only [Except.ok.injEq] at h
        subst h
        simp [mapM_except_length hl]

/-- **A `tcgen05.st` stores one value per source.** The shape is not `.packed16`, whose event
stores the values unpacked. -/
theorem fires_tcSt_len {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {pc : Nat}
    {e : Event} {o : Option TState} {ta a : Nat} {ss : List Opnd} {sh sh' : TcShape}
    {vals : List Value} (hsh : ∀ s, sh ≠ .packed16 s)
    (hf : Fires pc (eventTmpl A L g t (.tcSt ta ss sh)) e o)
    (hk : e.kind = .tc (.st a vals sh')) :
    vals.length = ss.length := by
  obtain ⟨u, _, hf⟩ := fires_tcSt_core hf hk (by intro h; cases h)
  rw [tcTmpl_tcSt_plain hsh] at hf
  cases ha : readBits L g u 32 (.reg ta) <;> cases hm : ss.mapM (readValue L g u 32) <;>
    simp only [ofExec, ha, hm, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hf <;>
    split_ifs at hf <;> simp only [Fires] at hf <;> rw [hf.1] at hk <;>
    simp only [reduceCtorEq, Kind.tc.injEq, TcKind.st.injEq] at hk
  rename_i vs _ _ _
  rw [← hk.2.1, mapM_except_length hm]

/-- A successful `mapM` in `Except` returns, at each position, the result of the element there. -/
theorem mapM_except_get {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r → ∀ {p : Nat} {x : α}, l[p]? = some x →
      ∃ y, f x = .ok y ∧ r[p]? = some y
  | [], r, _, p, x, hx => by simp at hx
  | a :: l, r, h, p, x, hx => by
    simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
    cases hb : f a with
    | error e => rw [hb] at h; cases h
    | ok b =>
      rw [hb] at h
      cases hl : l.mapM f with
      | error e => rw [hl] at h; cases h
      | ok bs =>
        rw [hl] at h
        simp only [Except.ok.injEq] at h
        subst h
        cases p with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          subst hx
          exact ⟨b, hb, rfl⟩
        | succ p =>
          simp only [List.getElem?_cons_succ] at hx ⊢
          exact mapM_except_get hl hx

/-- **A `tcgen05.st` stores its source registers' values.** -/
theorem fires_tcSt_vals {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {pc : Nat}
    {e : Event} {o : Option TState} {ta a : Nat} {ss : List Opnd} {sh sh' : TcShape}
    {vals : List Value} (hsh : ∀ s, sh ≠ .packed16 s)
    (hf : Fires pc (eventTmpl A L g t (.tcSt ta ss sh)) e o)
    (hk : e.kind = .tc (.st a vals sh'))
    {p r : Nat} {v : Value} (hs : ss[p]? = some (.reg r)) (hv : t.regs r = some v) :
    vals[p]? = some v := by
  obtain ⟨u, hu, hf⟩ := fires_tcSt_core hf hk (by intro h; cases h)
  rw [tcTmpl_tcSt_plain hsh] at hf
  cases ha : readBits L g u 32 (.reg ta) <;> cases hm : ss.mapM (readValue L g u 32) <;>
    simp only [ofExec, ha, hm, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hf <;>
    split_ifs at hf <;> simp only [Fires] at hf <;> rw [hf.1] at hk <;>
    simp only [reduceCtorEq, Kind.tc.injEq, TcKind.st.injEq] at hk
  rename_i vs _ _ _ _
  rw [← hk.2.1]
  obtain ⟨y, hy, hget⟩ := mapM_except_get hm hs
  simp only [readValue, readReg, hu, hv, pure, Except.pure, Except.ok.injEq] at hy
  rw [hget, hy]

end PTX.Flow
