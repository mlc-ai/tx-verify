-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.WriteSpace
public import Lemmas.Flow.NotObject
public import Lemmas.Flow.NotRead

@[expose] public section

/-! # The space and the CTA of a memory access

A proof tool. A read event is fired by a load instruction (`fires_read_op`), a write event by a
store or a Tensor Memory allocation (`fires_write_op`). Both address memory through `effAddr`,
in the space the instruction names; a shared address computed without cluster addressing is in
the thread's own CTA (`sharedEffAddr_local`). So a read is in its load's space (`loadSpace`), a
write in its store's (`storeSpace`), and a shared access is of the thread's CTA
(`fires_read_loc`, `fires_write_loc`). A kernel whose loads and stores all name shared memory
accesses only its threads' own CTAs' shared memory. A read of global memory is fired by a load
that names global memory or no space, also when its address is dynamic (`fires_read_global`). -/

namespace PTX.Flow

open PTX

noncomputable section

/-- The space an instruction reads, if it reads: the space a load names, shared memory for a
`movmatrix` that loads. -/
def loadSpace : Op → Option Space
  | .mem a => match a.kind with
    | .load => a.locSpace?
    | _ => none
  | .matrix m => match m.op with
    | .move mv => if mv.store then none else some .shared
    | _ => none
  | _ => none

/-- An effective address is in the space it is computed for; a shared one in the thread's CTA. -/
theorem effAddr_local {L : Launch} {g : Nat} {t : TState} {sp : Space} {base : Nat} {off : Int}
    {loc : Loc} (h : effAddr L g t sp base off = .ok loc) :
    loc.space = sp ∧ (sp = .shared → loc.cta = g / L.block) := by
  refine ⟨effAddr_space h, ?_⟩
  rintro rfl
  exact (sharedEffAddr_local (by simpa only [effAddr] using h)).2

/-- The access of a load is at its effective address. -/
theorem loadTmpl_loc {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {sp : Space}
    {nc : Bool} {w : Nat} {ds : List Nat} {base : Nat} {off : Int} {a : Acc}
    {k : List (Option Byte) → TState}
    (h : loadTmpl A L g t sp nc w ds base off = .read a k) :
    a.loc.space = sp ∧ (sp = .shared → a.loc.cta = g / L.block) := by
  unfold loadTmpl at h
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
        all_goals (simp only [Tmpl.read.injEq] at h; obtain ⟨rfl, -⟩ := h)
        all_goals exact effAddr_local (loc := loc) hloc

/-- The access of a store is at its effective address. -/
theorem storeTmpl_loc {L : Launch} {g : Nat} {t : TState} {sp : Space} {w : Nat}
    {base : Nat} {off : Int} {srcs : List Opnd} {a : Acc} {bs : List Byte} {u : TState}
    (h : storeTmpl L g t sp w base off srcs = .write a bs u) :
    a.loc.space = sp ∧ (sp = .shared → a.loc.cta = g / L.block) := by
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
        exact effAddr_local (loc := loc) hloc

/-- An atomic read-modify-write fires no read event of its own: its event is `.rmw` (`atomTmpl`). -/
theorem atomTmpl_noRead {A : List Assumption} {L : Launch} {g : Nat} {t : TState}
    {a : MemAccess} {acc : Acc} {k : List (Option Byte) → TState} :
    atomTmpl A L g t a ≠ .read acc k := by
  unfold atomTmpl
  dsimp only
  repeat' first
    | split
    | (intro h; cases h)

/-- A `movmatrix` that loads reads the `16` bytes of a row of the thread's own shared memory
window (`matrixMoveTmpl`). -/
theorem matrixMoveTmpl_read_spec {L : Launch} {g : Nat} {t : TState} {i : MatrixInstr}
    {m : MatrixMove} {a : Acc} {k : List (Option Byte) → TState}
    (h : matrixMoveTmpl L g t i m = .read a k) :
    a.loc.space = .shared ∧ a.loc.cta = g / L.block := by
  unfold matrixMoveTmpl at h
  dsimp only at h
  split at h
  · repeat' (first | split at h | cases h)
  · split at h
    · split at h
      · cases h
      · rename_i loc hl
        simp only [Tmpl.read.injEq] at h
        obtain ⟨rfl, -⟩ := h
        obtain ⟨h1, h2, -⟩ := matrixRowLoc_spec hl
        exact ⟨h1, h2⟩
    · cases h

/-- A `movmatrix` load reads a row of the thread's own shared memory window (`matrixTmpl`). -/
theorem matrixTmpl_read_spec {L : Launch} {g : Nat} {t : TState} {i : MatrixInstr}
    {a : Acc} {k : List (Option Byte) → TState} (h : matrixTmpl L g t i = .read a k) :
    a.loc.space = .shared ∧ a.loc.cta = g / L.block := by
  unfold matrixTmpl at h
  split at h
  · split at h
    · exact matrixMoveTmpl_read_spec h
    all_goals (first | (repeat' (first | split at h | cases h)))
  · cases h

/-- **A read is in its load's space**, of the thread's CTA when shared, unless the load is a
dynamic access. -/
theorem fires_read_loc {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {a : Acc} {bs : List (Option Byte)} (hk : e.kind = .rd a bs) :
    (loadSpace op = some a.loc.space ∧ (a.loc.space = .shared → a.loc.cta = g / L.block)) ∨
      dynamicAccess op = true := by
  by_cases hd : dynamicAccess op = true
  · exact .inr hd
  left
  obtain ⟨epc, ek⟩ := e
  simp only at hk
  subst hk
  obtain ⟨k, hm⟩ := fires_read_tmpl hf
  cases hq : readOp op
  · have hn := eventTmpl_notRead (A := A) (L := L) (g := g) (t := t) hq
    rw [hm] at hn
    exact hn.elim
  cases op <;> simp only [readOp, Bool.false_eq_true] at hq
  case mem ma =>
    simp only [eventTmpl, memTmpl] at hm
    split at hm
    · rename_i sp base _ _ hs _
      split at hm
      · have hk : ma.kind = .load := by assumption
        simp only [acquireLoadTmpl] at hm
        split at hm
        · rename_i a0 k0 h0
          simp only [Tmpl.read.injEq] at hm
          obtain ⟨rfl, -⟩ := hm
          obtain ⟨h1, h2⟩ := loadTmpl_loc h0
          exact ⟨by simp only [loadSpace, hk, hs, ← h1], fun hs' => h2 (h1 ▸ hs')⟩
        · rename_i hne
          exact absurd hm (hne a k)
      · have hk : ma.kind = .load := by assumption
        obtain ⟨h1, h2⟩ := loadTmpl_loc hm
        exact ⟨by simp only [loadSpace, hk, hs, h1], fun hs' => h2 (h1 ▸ hs')⟩
      · have hk : ma.kind = .store := by assumption
        simp [hk] at hq
      · have hk : ma.kind = .store := by assumption
        simp [hk] at hq
      · -- a strong access: only a load reads
        cases hk : ma.kind
        case load =>
          unfold accessTmpl at hm
          simp only [hk] at hm
          split at hm
          · cases hm
          · rename_i acc hacc
            split at hm
            · split at hm <;> cases hm
            · simp only [Tmpl.read.injEq] at hm
              obtain ⟨rfl, -⟩ := hm
              obtain ⟨h1, h2⟩ := accessAcc_local hs hacc
              exact ⟨by simp only [loadSpace, hk, hs, ← h1], fun hs' => h2 (h1 ▸ hs')⟩
        case store => simp [hk] at hq
        all_goals (simp [MemAccess.locSpace?, hk] at hs)
    · exact absurd hm atomTmpl_noRead
    · split at hm
      · exact absurd (dynamicAccess_of' (by assumption) (by assumption)) hd
      · cases hm
  case matrix i =>
    obtain ⟨h1, h2⟩ := matrixTmpl_read_spec hm
    cases hop : i.op
    case move mv =>
      simp only [hop] at hq
      have hstore : mv.store = false := by simpa using hq
      exact ⟨by simp [loadSpace, hop, hstore, h1], fun _ => h2⟩
    all_goals (simp only [hop] at hq; cases hq)

/-- **A read is in the space its load names**, also when the load is a dynamic access: a dynamic
access computes its footprint in the space it names (`accessAcc_local`). -/
theorem fires_read_space {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {a : Acc} {bs : List (Option Byte)} (hk : e.kind = .rd a bs) {sp : Space}
    (hs : loadSpace op = some sp) : a.loc.space = sp := by
  rcases fires_read_loc hf hk with ⟨h, -⟩ | hd
  · rw [hs] at h
    exact (Option.some.inj h).symm
  obtain ⟨epc, ek⟩ := e
  simp only at hk
  subst hk
  obtain ⟨k, hm⟩ := fires_read_tmpl hf
  cases op
  case mem ma =>
    have hl : ma.kind = .load ∧ ma.locSpace? = some sp := by
      cases hk2 : ma.kind <;> simp [loadSpace, hk2] at hs
      exact ⟨rfl, hs⟩
    simp only [eventTmpl, memTmpl] at hm
    split at hm
    · rename_i h1 h2 h3
      simp [dynamicAccess, h1, h2, h3] at hd
    · exact absurd hm atomTmpl_noRead
    · rename_i r _ _ _ _
      split at hm
      · rename_i hr
        unfold accessTmpl at hm
        simp only [hl.1] at hm
        split at hm
        · cases hm
        · rename_i acc hacc
          split at hm
          · split at hm <;> cases hm
          · simp only [Tmpl.read.injEq] at hm
            obtain ⟨rfl, -⟩ := hm
            exact (accessAcc_local hl.2 hacc).1
      · cases hm
  all_goals simp [dynamicAccess] at hd


/-- A shared address is in shared memory. -/
theorem readSharedAddress_shared {L : Launch} {g : Nat} {t : TState} {w : Nat}
    {generic cluster : Bool} {a : Opnd} {l : Loc}
    (h : readSharedAddress L g t w generic cluster a = .ok l) : l.space = .shared := by
  unfold readSharedAddress at h
  repeat' first
    | (simp only [bind, Except.bind, pure, Except.pure] at h; split at h)
    | split at h
  all_goals cases h
  all_goals rfl

/-- A shared effective address is in shared memory, with or without cluster addressing. -/
theorem sharedEffAddr_shared {L : Launch} {g : Nat} {t : TState} {cluster : Bool} {base : Nat}
    {off : Int} {l : Loc} (h : sharedEffAddr L g t cluster base off = .ok l) :
    l.space = .shared := by
  unfold sharedEffAddr at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · rename_i loc hl
        cases h
        exact readSharedAddress_shared (l := loc) hl
    · split at h
      · cases h
      · cases h; rfl

theorem absLoc_space {sp : Space} {o : Nat} {x off : Int} {loc : Loc}
    (h : absLoc sp o x off = .ok loc) : loc.space = sp := by
  unfold absLoc at h
  split_ifs at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  rfl

/-- **An access located in global memory names global memory or no space.** -/
theorem accessLoc_global {L : Launch} {g : Nat} {t : TState} {a : MemAccess} {loc : Loc}
    (h : accessLoc L g t a = .ok loc) (hg : loc.space = .global) :
    a.space = some .global ∨ a.space = none := by
  unfold accessLoc at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  split at h
  all_goals first
    | (left; assumption)
    | (right; assumption)
    | exfalso
  all_goals (repeat' (first | split at h | (cases h; done)))
  all_goals try (simp only [Except.ok.injEq] at h; subst h; cases hg)
  all_goals try (rw [absLoc_space (sp := .local) h] at hg; cases hg)
  all_goals try (rw [absLoc_space (sp := .const) h] at hg; cases hg)
  all_goals (rw [sharedEffAddr_shared h] at hg; cases hg)

/-- The footprint of an access is at its location. -/
theorem accessAcc_loc {L : Launch} {g : Nat} {t : TState} {a : MemAccess} {acc : Acc}
    (h : accessAcc L g t a = .ok acc) :
    ∃ loc, accessLoc L g t a = .ok loc ∧ acc.loc.space = loc.space := by
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
    obtain ⟨h1, -⟩ := elemAcc_local h0
    subst he
    exact ⟨loc, rfl, by simp only [semAcc_loc]; exact h1⟩

/-- **A read of global memory is fired by a load that names global memory or no space.** -/
theorem fires_read_global {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {a : Acc} {bs : List (Option Byte)} (hk : e.kind = .rd a bs) (hg : a.loc.space = .global) :
    ∃ ma, op = .mem ma ∧ (ma.space = some .global ∨ ma.space = none) := by
  rcases fires_read_loc hf hk with ⟨h, -⟩ | hd
  · rw [hg] at h
    cases op
    case mem ma =>
      refine ⟨ma, rfl, .inl ?_⟩
      simp only [loadSpace] at h
      split at h
      · unfold MemAccess.locSpace? at h
        split at h
        · split at h
          · rename_i hs _; exact hs
          · cases h
          · cases h
        · cases h
      · cases h
    case matrix m =>
      simp only [loadSpace] at h
      split at h
      · split at h <;> cases h
      · cases h
    all_goals simp [loadSpace] at h
  obtain ⟨epc, ek⟩ := e
  simp only at hk
  subst hk
  obtain ⟨k, hm⟩ := fires_read_tmpl hf
  cases op
  case mem ma =>
    refine ⟨ma, rfl, ?_⟩
    have hkd : ma.kind = .load := by
      have hr := fires_read_op hf rfl
      simp only [readOp] at hr
      split at hr
      · assumption
      · cases hr
    simp only [eventTmpl, memTmpl] at hm
    split at hm
    · rename_i h1 h2 h3
      simp [dynamicAccess, h1, h2, h3] at hd
    · exact absurd hm atomTmpl_noRead
    · split at hm
      · unfold accessTmpl at hm
        simp only [hkd] at hm
        split at hm
        · cases hm
        · rename_i acc hacc
          split at hm
          · split at hm <;> cases hm
          · simp only [Tmpl.read.injEq] at hm
            obtain ⟨rfl, -⟩ := hm
            obtain ⟨loc, hl, hs⟩ := accessAcc_loc hacc
            exact accessLoc_global hl (hs.symm.trans hg)
      · cases hm
  all_goals simp [dynamicAccess] at hd
/-- **A write is in its store's space**, of the thread's CTA when shared, unless the store is a
dynamic access. -/
theorem fires_write_loc {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    {a : Acc} {bs : List Byte} (hk : e.kind = .wr a bs) :
    (storeSpace op = some a.loc.space ∧ (a.loc.space = .shared → a.loc.cta = g / L.block)) ∨
      dynamicAccess op = true := by
  rcases fires_write_space hf hk with hsp | hd
  swap
  · exact .inr hd
  by_cases hd : dynamicAccess op = true
  · exact .inr hd
  left
  refine ⟨hsp, fun hsh => ?_⟩
  have hop := fires_write_op hf hk
  obtain ⟨epc, ek⟩ := e
  simp only at hk
  subst hk
  rcases fires_write_tmpl hf with ⟨u, hm⟩ | ⟨u, hm, -⟩
  swap
  · cases op <;> simp only [writeOp, Bool.false_eq_true] at hop
    case mem ma =>
      have := memTmpl_isMem (A := A) (L := L) (g := g) (t := t) (a := ma)
      simp only [eventTmpl] at hm
      rw [hm] at this
      exact this.elim
    case matrix m =>
      simp only [eventTmpl, matrixTmpl, matrixMoveTmpl] at hm
      repeat' (first | split at hm | cases hm)
    case tcAlloc group base off nc =>
      simp only [eventTmpl, tcTmpl, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw] at hm
      repeat' (first | split at hm | (simp [ofExec] at hm; done))
      simp only [ofExec, Tmpl.tcAllocStore.injEq] at hm
      obtain ⟨hloc, -⟩ := hm
      rw [← hloc]
      exact (effAddr_local (by assumption)).2 rfl
  cases op <;> simp only [writeOp, Bool.false_eq_true] at hop
  case mem ma =>
    simp only [eventTmpl, memTmpl] at hm
    split at hm
    · rename_i sp base _ _ hs _
      split at hm
      · have hk : ma.kind = .load := by assumption
        simp [hk] at hop
      · have hk : ma.kind = .load := by assumption
        simp [hk] at hop
      · simp only [releaseStoreTmpl] at hm
        split at hm
        · rename_i a0 bs0 t0 h0
          simp only [Tmpl.write.injEq] at hm
          obtain ⟨rfl, -, -⟩ := hm
          obtain ⟨h1, h2⟩ := storeTmpl_loc h0
          exact h2 (h1 ▸ hsh)
        · rename_i hne
          exact absurd hm (hne a bs u)
      · obtain ⟨h1, h2⟩ := storeTmpl_loc hm
        exact h2 (h1 ▸ hsh)
      · -- a strong access
        cases hk : ma.kind
        case store =>
          unfold accessTmpl at hm
          simp only [hk] at hm
          split at hm
          · cases hm
          · rename_i acc hacc
            repeat' (first | split at hm | (cases hm; done))
            simp only [Tmpl.write.injEq] at hm
            obtain ⟨rfl, -, -⟩ := hm
            obtain ⟨h1, h2⟩ := accessAcc_local hs hacc
            exact h2 (h1 ▸ hsh)
        case load => simp [hk] at hop
        all_goals (simp [MemAccess.locSpace?, hk] at hs)
    · exact absurd hm atomTmpl_noWrite
    · split at hm
      · exact absurd (dynamicAccess_of' (by assumption) (by assumption)) hd
      · cases hm
  case matrix i => exact (matrixTmpl_write_spec hm).2.1
  case tcAlloc group base off nc =>
    simp only [eventTmpl, tcTmpl, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hm
    repeat' (first | split at hm | simp [ofExec] at hm)

/-- Whether an instruction may access memory outside shared memory: it loads or stores a space other
than shared memory, or it is a dynamic access. -/
def globalMemOp (op : Op) : Bool :=
  !(loadSpace op == none || loadSpace op == some .shared) ||
    !(storeSpace op == none || storeSpace op == some .shared) || dynamicAccess op

/-- An instruction that accesses only shared memory names shared memory. -/
theorem globalMemOp_space {op : Op} {sp : Space} (hg : globalMemOp op = false)
    (hs : loadSpace op = some sp ∨ storeSpace op = some sp) : sp = .shared := by
  simp only [globalMemOp, Bool.or_eq_false_iff, Bool.not_eq_false', Bool.or_eq_true,
    beq_iff_eq] at hg
  rcases hs with hs | hs <;> simp_all

/-- An instruction that accesses only shared memory is not a dynamic access. -/
theorem globalMemOp_dynamic {op : Op} (hg : globalMemOp op = false) : dynamicAccess op = false := by
  simp only [globalMemOp, Bool.or_eq_false_iff] at hg
  exact hg.2

end

end PTX.Flow
