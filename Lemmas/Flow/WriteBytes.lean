-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.WriteSpace
public import Lemmas.Flow.Fire

@[expose] public section

/-! # The bytes and the semantics of a write

A proof tool. A write event is fired by a store's element template, which writes the bytes of a
value as wide as the element (`storeTmpl`), by an allocation's store of its 4-byte address, or by a
`movmatrix` row store, whose row is 16 bytes (`matrixMoveTmpl`) and whose register state this step
need not fill (`sizedWrite`). So a write carries as many bytes as its footprint
(`fires_write_length`), and it releases only when the instruction is a release store
(`fires_write_release`). -/

namespace PTX.Flow

open PTX

noncomputable section

/-- A stored value is as wide as the element the store writes (`storeValue`). -/
theorem storeValue_bytes {w : Nat} {v v' : Value} (h : storeValue w v = .ok v') :
    v'.bytes = w / 8 := by
  unfold storeValue at h
  split at h
  · rename_i hv
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact hv
  · split at h
    · split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        rfl
      · cases h
    · cases h

/-- A store writes a value as wide as its element also when the value comes from a read
(`storeValue`). -/
theorem bind_storeValue_bytes {w : Nat} {r : Exec Value} {v' : Value}
    (h : (r >>= storeValue w) = .ok v') : v'.bytes = w / 8 := by
  cases r with
  | error f => simp only [bind, Except.bind] at h; cases h
  | ok v => exact storeValue_bytes h

/-- Whether an instruction writes with release semantics: a store with `.release` or `.acq_rel`
semantics, which its footprint releases (`MemAccess.semAcc`). -/
def releaseOp : Op → Bool
  | .mem a => match a.kind, a.sem with
    | .store, .release | .store, .acqRel => true
    | _, _ => false
  | _ => false

/-- A store is a release store exactly at `.release` or `.acq_rel` semantics (`releaseOp`). -/
theorem releaseOp_mem {a : MemAccess} (hk : a.kind = .store) :
    releaseOp (.mem a) = true ↔ a.sem = .release ∨ a.sem = .acqRel := by
  simp only [releaseOp, hk]
  cases a.sem <;> simp

/-- Whether an instruction's writes are as wide as their footprint: every write but a `movmatrix`
row store, whose row is the 16 bytes of a shared memory row of registers a step of the warp fills
(`matrixMoveTmpl`). -/
def sizedWrite : Op → Bool
  | .matrix m => match m.op with
    | .move mv => !mv.store
    | _ => true
  | _ => true

theorem storeTmpl_bytes {L : Launch} {g : Nat} {t : TState} {sp : Space} {w : Nat}
    {base : Nat} {off : Int} {srcs : List Opnd} {a : Acc} {bs : List Byte} {u : TState}
    (h : storeTmpl L g t sp w base off srcs = .write a bs u) :
    bs.length = a.size ∧ a.release = false := by
  unfold storeTmpl at h
  split at h
  · cases h
  · rename_i a' heq
    have hrel := (bind_elemAcc heq).1
    simp only [bind, Except.bind] at heq
    split at heq
    · cases heq
    · rename_i loc hloc
      unfold elemAcc at heq
      split at heq
      · cases heq
      · simp only [pure, Except.pure, Except.ok.injEq] at heq
        subst heq
        repeat' (first | split at h | (cases h; done))
        simp only [Tmpl.write.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        rename_i v _ hv
        exact ⟨by simpa [Value.toBytes] using bind_storeValue_bytes hv, rfl⟩

/-- The memory semantics an access adds to its element's footprint keep its size
(`MemAccess.semAcc`). -/
theorem semAcc_size (a : MemAccess) (acc : Acc) : (a.semAcc acc).size = acc.size := by
  cases h : a.sem <;> simp [MemAccess.semAcc, h]

/-- The footprint of an access located by `accessLoc` is one element wide. -/
theorem accessAcc_size {L : Launch} {g : Nat} {t : TState} {a : MemAccess} {acc : Acc}
    (h : accessAcc L g t a = .ok acc) : acc.size = a.elem.width / 8 := by
  have hmap : ∀ {α : Type} {f : α → Acc} {x : Exec α} {r : Acc}, f <$> x = .ok r →
      ∃ y, x = .ok y ∧ f y = r := by
    intro α f x r hx
    cases x with
    | error e => simp at hx
    | ok y => exact ⟨y, rfl, by simpa using hx⟩
  unfold accessAcc at h
  simp only [bind, Except.bind] at h
  repeat' (first | split at h | contradiction)
  obtain ⟨acc0, h0, he⟩ := hmap h
  unfold elemAcc at h0
  split at h0
  · cases h0
  · simp only [pure, Except.pure, Except.ok.injEq] at h0
    subst h0
    subst he
    simp only [semAcc_size]

/-- A write of an access located by `accessLoc`, or of a `st.bulk`, carries as many bytes as its
footprint, and releases only when it is a store with `.release` or `.acq_rel` semantics
(`MemAccess.semAcc`). -/
theorem accessTmpl_bytes {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {ma : MemAccess} {a : Acc} {bs : List Byte} {u : TState}
    (h : accessTmpl A L g t ma = .write a bs u) :
    bs.length = a.size ∧
      (a.release = true ↔ ma.kind = .store ∧ (ma.sem = .release ∨ ma.sem = .acqRel)) := by
  unfold accessTmpl bulkInitTmpl at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · simp only [Tmpl.write.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      obtain hk : ma.kind = .bulkInit := by assumption
      exact ⟨by simp, by simp [hk]⟩
  · repeat' (first | split at h | cases h)
  · split at h
    · cases h
    · rename_i acc hacc
      repeat' (first | split at h | (cases h; done))
      simp only [Tmpl.write.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      rename_i v _ hv
      obtain ⟨acc0, he, -, hrel, -⟩ := accessAcc_semAcc hacc
      obtain hk : ma.kind = .store := by assumption
      refine ⟨by simpa [Value.toBytes, accessAcc_size hacc] using bind_storeValue_bytes hv, ?_⟩
      rw [← he]
      simpa [hk] using MemAccess.semAcc_release ma acc0 hrel
  · cases h

/-- A write of an access located by `accessLoc` does not release unless the instruction is a
release store (`releaseOp`). -/
theorem release_of_access {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {ma : MemAccess} {a : Acc} {bs : List Byte} {u : TState}
    (hm : accessTmpl A L g t ma = .write a bs u) (hr : releaseOp (.mem ma) = false) :
    a.release = false := by
  by_cases hk : ma.kind = .store
  · have hnot : ¬(ma.sem = .release ∨ ma.sem = .acqRel) := by
      have hp : ¬(releaseOp (.mem ma) = true) := by simpa using hr
      exact (releaseOp_mem hk).not.mp hp
    by_cases h : a.release = true
    · exact absurd ((accessTmpl_bytes hm).2.mp h).2 hnot
    · simpa using h
  · by_cases h : a.release = true
    · exact absurd ((accessTmpl_bytes hm).2.mp h).1 hk
    · simpa using h

/-- **A write carries as many bytes as its footprint** (`sizedWrite`). -/
theorem fires_write_length {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {a : Acc} {bs : List Byte} (hk : e.kind = .wr a bs) (hs : sizedWrite op = true) :
    bs.length = a.size := by
  have hop := fires_write_op hf hk
  obtain ⟨epc, ek⟩ := e
  simp only at hk
  subst hk
  rcases fires_write_tmpl hf with ⟨u, hm⟩ | ⟨u, hm, ha⟩
  · cases op <;> simp only [writeOp, Bool.false_eq_true] at hop
    case mem ma =>
      simp only [eventTmpl, memTmpl] at hm
      split at hm
      · split at hm
        · have hk : ma.kind = .load := by assumption
          simp [hk] at hop
        · have hk : ma.kind = .load := by assumption
          simp [hk] at hop
        · simp only [releaseStoreTmpl] at hm
          split at hm
          · rename_i a0 bs0 t0 h0
            simp only [Tmpl.write.injEq] at hm
            obtain ⟨rfl, rfl, -⟩ := hm
            exact (storeTmpl_bytes h0).1
          · rename_i hne
            exact absurd hm (hne a bs u)
        · exact (storeTmpl_bytes hm).1
        · cases hk : ma.kind
          case store => exact (accessTmpl_bytes hm).1
          case bulkInit => exact (accessTmpl_bytes hm).1
          all_goals (simp only [accessTmpl, hk] at hm; repeat' (first | split at hm | cases hm))
      · exact absurd hm atomTmpl_noWrite
      · split at hm
        · exact (accessTmpl_bytes hm).1
        · cases hm
    case matrix m =>
      cases hmo : m.op
      case move mv =>
        simp only [hmo] at hop
        simp only [sizedWrite, hmo, Bool.not_eq_true'] at hs
        simp only [hop] at hs
        exact absurd hs (by simp)
      all_goals (simp only [hmo] at hop; cases hop)
    case tcAlloc group base off nc =>
      simp only [eventTmpl, tcTmpl, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw] at hm
      repeat' (first | split at hm | simp [ofExec] at hm)
  · simp only [Fires, hm] at hf
    obtain ⟨col, -, he, -⟩ := hf
    simp only [Event.mk.injEq, Kind.wr.injEq] at he
    obtain ⟨-, h1, rfl⟩ := he
    rw [h1]
    simp [Value.toBytes, Value.bytes]

/-- **A write releases only at a release store** (`releaseOp`). -/
theorem fires_write_release {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {a : Acc} {bs : List Byte} (hk : e.kind = .wr a bs) (hr : releaseOp op = false) :
    a.release = false := by
  have hop := fires_write_op hf hk
  obtain ⟨epc, ek⟩ := e
  simp only at hk
  subst hk
  rcases fires_write_tmpl hf with ⟨u, hm⟩ | ⟨u, hm, ha⟩
  · cases op <;> simp only [writeOp, releaseOp, Bool.false_eq_true] at hop hr
    case mem ma =>
      simp only [eventTmpl, memTmpl] at hm
      split at hm
      · split at hm
        · have hk : ma.kind = .load := by assumption
          simp [hk] at hop
        · have hk : ma.kind = .load := by assumption
          simp [hk] at hop
        · have hk : ma.kind = .store := by assumption
          have hs : ma.sem = .release := by assumption
          simp [hk, hs] at hr
        · exact (storeTmpl_bytes hm).2
        · exact release_of_access hm hr
      · exact absurd hm atomTmpl_noWrite
      · split at hm
        · exact release_of_access hm hr
        · cases hm
    case matrix m => exact (matrixTmpl_write_spec hm).2.2.2
    case tcAlloc group base off nc =>
      simp only [eventTmpl, tcTmpl, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw] at hm
      repeat' (first | split at hm | simp [ofExec] at hm)
  · rw [ha]

end

end PTX.Flow
