-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.NotClc

@[expose] public section

/-! # The space a store writes

A proof tool. A write event is fired by a store instruction, in the space it names, or by a
Tensor Memory allocation storing its address to shared memory (`fires_write_space`). So a kernel
whose stores all name shared memory writes only shared memory from its threads. -/

namespace PTX.Flow

open PTX

noncomputable section

/-- The space an instruction writes, if it writes: the space a store names, shared memory for a
`movmatrix` that stores or a Tensor Memory allocation's address store. -/
def storeSpace : Op → Option Space
  | .mem a => match a.kind with
    | .load => none
    | _ => a.locSpace?
  | .matrix m => match m.op with
    | .move mv => if mv.store then some .shared else none
    | _ => none
  | .tcAlloc .. => some .shared
  | _ => none

/-- An atomic read-modify-write fires no write event of its own: its event is `.rmw`
(`atomTmpl`). -/
theorem atomTmpl_noWrite {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {a : MemAccess} {acc : Acc} {bs : List Byte} {u : TState} :
    atomTmpl A L g t a ≠ .write acc bs u := by
  unfold atomTmpl
  dsimp only
  repeat' first
    | split
    | (intro h; cases h)

/-- The row location of a `movmatrix` is in the thread's own shared memory window, at a
`16`-byte aligned address (`matrixRowLoc`). -/
theorem matrixRowLoc_spec {L : Launch} {g : Nat} {t : TState} {i : MatrixInstr} {loc : Loc}
    (h : matrixRowLoc L g t i = .ok loc) :
    loc.space = .shared ∧ loc.cta = g / L.block ∧ loc.addr % 16 = 0 := by
  unfold matrixRowLoc at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' (first | split at h | (cases h; done))
  all_goals (simp only [Except.ok.injEq] at h; subst h; simp_all)

/-- A `movmatrix` that stores writes the `16` bytes of a row of the thread's own shared memory
window, without releasing (`matrixMoveTmpl`). -/
theorem matrixMoveTmpl_write_spec {L : Launch} {g : Nat} {t : TState} {i : MatrixInstr}
    {m : MatrixMove} {a : Acc} {bs : List Byte} {u : TState}
    (h : matrixMoveTmpl L g t i m = .write a bs u) :
    a.loc.space = .shared ∧ a.loc.cta = g / L.block ∧ a.size = 16 ∧ a.release = false := by
  unfold matrixMoveTmpl at h
  dsimp only at h
  split at h
  · split at h
    · split at h <;> cases h
    · split at h
      · cases h
      · rename_i loc hl
        simp only [Tmpl.write.injEq] at h
        obtain ⟨rfl, -, -⟩ := h
        obtain ⟨h1, h2, -⟩ := matrixRowLoc_spec hl
        exact ⟨h1, h2, rfl, rfl⟩
  · split at h
    · split at h <;> cases h
    · cases h

/-- A `movmatrix` store writes the `16` bytes of a row of the thread's own shared memory window,
without releasing (`matrixTmpl`). -/
theorem matrixTmpl_write_spec {L : Launch} {g : Nat} {t : TState} {i : MatrixInstr}
    {a : Acc} {bs : List Byte} {u : TState} (h : matrixTmpl L g t i = .write a bs u) :
    a.loc.space = .shared ∧ a.loc.cta = g / L.block ∧ a.size = 16 ∧ a.release = false := by
  unfold matrixTmpl at h
  split at h
  · split at h
    · exact matrixMoveTmpl_write_spec h
    all_goals (first | (split at h <;> cases h) | cases h)
  · cases h

/-- An effective address is in the space it is computed for. -/
theorem effAddr_space {L : Launch} {g : Nat} {t : TState} {sp : Space} {base : Nat} {off : Int}
    {loc : Loc} (h : effAddr L g t sp base off = .ok loc) : loc.space = sp := by
  cases sp with
  | global =>
    simp only [effAddr, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · cases h; rfl
  | shared =>
    simp only [effAddr, sharedEffAddr, bind, Except.bind, pure, Except.pure] at h
    repeat' (first | split at h | (cases h; done))
    all_goals (simp only [Except.ok.injEq] at h; subst h)
    · rename_i hl
      unfold readSharedAddress at hl
      simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hl
      repeat' (first | split at hl | (cases hl; done))
      all_goals (simp only [Except.ok.injEq] at hl; subst hl; rfl)
    · rfl
  | «local» | const => cases h

/-- A location `accessLoc` finds by a direct address is in the space the access names, in the
thread's own CTA when that is shared (`MemAccess.locSpace?`). -/
theorem accessLoc_local {L : Launch} {g : Nat} {t : TState} {a : MemAccess} {sp : Space}
    {loc : Loc} (hs : a.locSpace? = some sp) (h : accessLoc L g t a = .ok loc) :
    loc.space = sp ∧ (sp = .shared → loc.cta = g / L.block) := by
  unfold accessLoc at h
  unfold MemAccess.locSpace? at hs
  split at hs
  · split at hs
    · rename_i hsp hb
      simp only [hsp, hb] at h
      simp only [Option.some.injEq] at hs
      subst hs
      exact ⟨effAddr_space h, fun hc => by cases hc⟩
    · rename_i hsp hb
      simp only [hsp, hb] at h
      simp only [Option.some.injEq] at hs
      subst hs
      simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw] at h
      repeat' (first | split at h | (cases h; done))
      all_goals first
        | (have hl := sharedEffAddr_local h
           exact ⟨hl.1, fun _ => hl.2⟩)
        | (simp only [Except.ok.injEq] at h
           subst h
           exact ⟨rfl, fun _ => rfl⟩)
    · cases hs
  · cases hs

/-- The memory semantics an access adds to its element's footprint keep its location
(`MemAccess.semAcc`). -/
theorem semAcc_loc (a : MemAccess) (acc : Acc) : (a.semAcc acc).loc = acc.loc := by
  cases h : a.sem <;> simp [MemAccess.semAcc, h]

/-- The footprint of an element is at the element's location. -/
theorem elemAcc_local {loc : Loc} {n c j : Nat} {acc : Acc} (h : elemAcc loc n c j = .ok acc) :
    acc.loc.space = loc.space ∧ acc.loc.cta = loc.cta := by
  unfold elemAcc at h
  split at h
  · cases h
  · cases h
    exact ⟨rfl, rfl⟩

/-- The footprint of a directly located access is in the space the access names, in the thread's
own CTA when that is shared (`accessLoc_local`). -/
theorem accessAcc_local {L : Launch} {g : Nat} {t : TState} {a : MemAccess} {sp : Space}
    {acc : Acc} (hs : a.locSpace? = some sp) (h : accessAcc L g t a = .ok acc) :
    acc.loc.space = sp ∧ (sp = .shared → acc.loc.cta = g / L.block) := by
  have hmap : ∀ {α : Type} {f : α → Acc} {x : Exec α} {r : Acc}, f <$> x = .ok r →
      ∃ y, x = .ok y ∧ f y = r := by
    intro α f x r hx
    cases x with
    | error e => simp at hx
    | ok y => exact ⟨y, rfl, by simpa using hx⟩
  unfold accessAcc at h
  simp only [bind, Except.bind] at h
  cases hl : accessLoc L g t a with
  | error f => simp only [hl, reduceCtorEq] at h
  | ok loc =>
    simp only [hl] at h
    repeat' (first | split at h | contradiction)
    obtain ⟨acc0, h0, he⟩ := hmap h
    obtain ⟨h1, h2⟩ := elemAcc_local h0
    obtain ⟨h3, h4⟩ := accessLoc_local hs hl
    subst he
    simp only [semAcc_loc]
    exact ⟨by rw [h1]; exact h3, fun hs' => by rw [h2]; exact h4 hs'⟩

/-- A store's write is in the space it names. -/
theorem storeTmpl_space {L : Launch} {g : Nat} {t : TState} {sp : Space} {w : Nat}
    {base : Nat} {off : Int} {srcs : List Opnd} {a : Acc} {bs : List Byte} {u : TState}
    (h : storeTmpl L g t sp w base off srcs = .write a bs u) : a.loc.space = sp := by
  unfold storeTmpl at h
  split at h
  · cases h
  · rename_i a' heq
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
        obtain ⟨rfl, -, -⟩ := h
        simp only [Loc.at]
        exact effAddr_space hloc

/-- A write event is fired by a writing template or an allocation's address store. -/
theorem fires_write_tmpl {pc : Nat} {m : Tmpl} {epc : Nat} {a : Acc} {bs : List Byte}
    {o : Option TState} (hf : Fires pc m ⟨epc, .wr a bs⟩ o) :
    (∃ u, m = .write a bs u) ∨ ∃ u, m = .tcAllocStore a.loc u ∧ a = { loc := a.loc, size := 4 } :=
      by
  cases m <;> simp only [Fires] at hf
  case write => exact .inl ⟨_, by aesop⟩
  case tcAllocStore dst u =>
    obtain ⟨col, -, he, -⟩ := hf
    simp only [Event.mk.injEq, Kind.wr.injEq] at he
    obtain ⟨-, rfl, -⟩ := he
    exact .inr ⟨u, rfl, rfl⟩
  all_goals aesop

/-- A read event is fired by a read template. -/
theorem fires_read_tmpl {pc : Nat} {m : Tmpl} {epc : Nat} {a : Acc} {bs : List (Option Byte)}
    {o : Option TState} (hf : Fires pc m ⟨epc, .rd a bs⟩ o) : ∃ k, m = .read a k := by
  cases m <;> simp only [Fires] at hf <;> aesop

/-- **A write is in its store's space.** A write event is fired by a store, in the space it names,
or by a `movmatrix` store or a Tensor Memory allocation, in shared memory, unless the store is a
dynamic access. -/
theorem fires_write_space {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {a : Acc} {bs : List Byte} (hk : e.kind = .wr a bs) :
    storeSpace op = some a.loc.space ∨ dynamicAccess op = true := by
  by_cases hd : dynamicAccess op = true
  · exact .inr hd
  left
  have hop := fires_write_op hf hk
  obtain ⟨epc, ek⟩ := e
  simp only at hk
  subst hk
  rcases fires_write_tmpl hf with ⟨u, hm⟩ | ⟨u, hm, -⟩
  swap
  · cases op
    case mem a =>
      have h := memTmpl_isMem (A := A) (L := L) (g := g) (t := t) (a := a)
      simp only [eventTmpl] at hm
      rw [hm] at h
      exact h.elim
    all_goals simp only [writeOp, Bool.false_eq_true] at hop
    case matrix m =>
      simp only [eventTmpl, matrixTmpl, matrixMoveTmpl] at hm
      repeat' (first | split at hm | cases hm)
    case tcAlloc group base off nc =>
      simp only [eventTmpl, tcTmpl, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw] at hm
      repeat' (first | split at hm | (simp [ofExec] at hm; done))
      simp only [ofExec, Tmpl.tcAllocStore.injEq] at hm
      obtain ⟨hloc, -⟩ := hm
      simp only [storeSpace]
      rw [← hloc, effAddr_space (by assumption)]
  cases op <;> simp only [writeOp, Bool.false_eq_true] at hop
  case mem m =>
    simp only [eventTmpl, memTmpl] at hm
    split at hm
    · rename_i sp base _ _ hs _
      split at hm
      · have hk : m.kind = .load := by assumption
        simp [hk] at hop
      · have hk : m.kind = .load := by assumption
        simp [hk] at hop
      · have hk : m.kind = .store := by assumption
        simp only [releaseStoreTmpl] at hm
        split at hm
        · rename_i a0 bs0 t0 h0
          simp only [Tmpl.write.injEq] at hm
          obtain ⟨rfl, -, -⟩ := hm
          simp only [storeSpace, hk, storeTmpl_space h0]
          assumption
        · rename_i hne
          exact absurd hm (hne a bs u)
      · have hk : m.kind = .store := by assumption
        simp only [storeSpace, hk, storeTmpl_space hm]
        assumption
      · -- a strong access: `accessTmpl` writes at the footprint `accessAcc` computes
        cases hk : m.kind
        case store =>
          simp only [accessTmpl, hk] at hm
          split at hm
          · cases hm
          · rename_i acc hacc
            repeat' (first | split at hm | (cases hm; done))
            simp only [Tmpl.write.injEq] at hm
            obtain ⟨rfl, -, -⟩ := hm
            obtain ⟨h1, -⟩ := accessAcc_local hs hacc
            simp only [storeSpace, hk, hs, h1]
        case load =>
          simp only [accessTmpl, hk] at hm
          repeat' (first | split at hm | cases hm)
        all_goals (simp [MemAccess.locSpace?, hk] at hs)
    · exact absurd hm atomTmpl_noWrite
    · split at hm
      · exact absurd (dynamicAccess_of' (by assumption) (by assumption)) hd
      · cases hm
  case matrix m =>
    have hsp := matrixTmpl_write_spec hm
    cases hmv : m.op
    case move mv =>
      simp only [hmv] at hop
      have hstore : mv.store = true := by simpa using hop
      simp only [storeSpace, hmv, hstore, ite_true, hsp.1]
    all_goals (simp only [hmv] at hop; cases hop)
  case tcAlloc group base off nc =>
    simp only [eventTmpl, tcTmpl, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hm
    repeat' (first | split at hm | simp [ofExec] at hm)

end

end PTX.Flow
