-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run

@[expose] public section

/-! # The event templates of the memory and warp families

A proof tool. `memTmpl` and `warpTmpl` dispatch on the family rule (PROG-RULE-ID). For an access
or a collective whose rule is known these lemmas give the template the rule selects: a weak load,
an acquire load, a weak store or a release store (THREAD-ACCESS), an atomic read-modify-write
(THREAD-ATOMIC), a shuffle, a ballot, an election or a warp barrier. Every memory template is a
read, a non-coherent read, a write, an atomic read-modify-write or undefined behaviour
(`memTmpl_isMem`).
-/

namespace PTX

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState}

section Mem

/-- The shapes of a memory template: a read, a non-coherent read, a write, an atomic
read-modify-write or undefined behaviour. -/
def Tmpl.IsMem : Tmpl → Prop
  | .read .. | .readNC .. | .write .. | .rmw .. | .ub _ => True
  | _ => False

/-- A load is a read, a non-coherent read or undefined behaviour. -/
theorem loadTmpl_isMem {sp : Space} {nc : Bool} {w : Nat} {ds : List Nat} {base : Nat}
    {off : Int} : (loadTmpl A L g t sp nc w ds base off).IsMem := by
  unfold loadTmpl; repeat' first | trivial | split

/-- A store is a write or undefined behaviour. -/
theorem storeTmpl_isMem {sp : Space} {w : Nat} {base : Nat} {off : Int} {srcs : List Opnd} :
    (storeTmpl L g t sp w base off srcs).IsMem := by
  unfold storeTmpl; repeat' first | trivial | split

/-- An acquire load is a read or undefined behaviour. -/
theorem acquireLoadTmpl_isMem {sc : MbarScope} {sp : Space} {w d base : Nat} {off : Int} :
    (acquireLoadTmpl A L g t sc sp w d base off).IsMem := by
  have h := loadTmpl_isMem (A := A) (L := L) (g := g) (t := t) (sp := sp) (nc := false) (w := w)
    (ds := [d]) (base := base) (off := off)
  unfold acquireLoadTmpl
  generalize loadTmpl A L g t sp false w [d] base off = m at h ⊢
  cases m <;> trivial

/-- A release store is a write or undefined behaviour. -/
theorem releaseStoreTmpl_isMem {sc : MbarScope} {sp : Space} {w base : Nat} {off : Int}
    {v : Opnd} : (releaseStoreTmpl L g t sc sp w base off v).IsMem := by
  have h := storeTmpl_isMem (L := L) (g := g) (t := t) (sp := sp) (w := w) (base := base)
    (off := off) (srcs := [v])
  unfold releaseStoreTmpl
  generalize storeTmpl L g t sp w base off [v] = m at h ⊢
  cases m <;> trivial

/-- The template of a weak access: a read without `.acquire`, a non-coherent read, a write
without `.release`, or undefined behaviour. -/
def Tmpl.IsWeakMem : Tmpl → Prop
  | .read a _ => a.acquire = false
  | .readNC .. | .ub _ => True
  | .write a _ _ => a.release = false
  | _ => False

/-- An element footprint carries none of the qualifiers of a strong access: no `.acquire`, no
`.release` and no `.relaxed` (`Acc.Strong`). -/
theorem elemAcc_weak {loc : Loc} {n c j : Nat} {acc : Acc} (h : elemAcc loc n c j = .ok acc) :
    acc.acquire = false ∧ acc.release = false ∧ acc.relaxed = false := by
  unfold elemAcc at h
  split at h
  · cases h
  · cases h; exact ⟨rfl, rfl, rfl⟩

/-- The footprint `accessAcc` computes for an access is its element's footprint with the access's
memory semantics (`MemAccess.semAcc`), and an element footprint carries none of the qualifiers of
a strong access. -/
theorem accessAcc_semAcc {a : MemAccess} {acc : Acc} (h : accessAcc L g t a = .ok acc) :
    ∃ acc0, a.semAcc acc0 = acc ∧ acc0.acquire = false ∧ acc0.release = false ∧
      acc0.relaxed = false := by
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
  obtain ⟨h1, h2, h3⟩ := elemAcc_weak h0
  exact ⟨acc0, he, h1, h2, h3⟩

/-- The footprint of an element of a weak access carries none of the qualifiers of a strong
access: `accessAcc` adds the access's memory semantics to the element's footprint
(`MemAccess.semAcc`), and `.weak` adds none. -/
theorem accessAcc_weak {a : MemAccess} {acc : Acc} (h : accessAcc L g t a = .ok acc)
    (hsem : a.sem = .weak) :
    acc.acquire = false ∧ acc.release = false ∧ acc.relaxed = false := by
  obtain ⟨acc0, he, h1, h2, h3⟩ := accessAcc_semAcc h
  have hs : a.semAcc acc0 = acc0 := by simp [MemAccess.semAcc, hsem]
  rw [← he, hs]
  exact ⟨h1, h2, h3⟩

/-- `MemAccess.semAcc` sets the `.acquire` flag exactly for the `.acquire` and `.acq_rel`
semantics, when the footprint it extends carries no `.acquire`. -/
theorem MemAccess.semAcc_acquire (a : MemAccess) (acc : Acc) (h : acc.acquire = false) :
    (a.semAcc acc).acquire = true ↔ a.sem = .acquire ∨ a.sem = .acqRel := by
  cases hs : a.sem <;> simp [MemAccess.semAcc, hs, h]

/-- `MemAccess.semAcc` sets the `.release` flag exactly for the `.release` and `.acq_rel`
semantics, when the footprint it extends carries no `.release`. -/
theorem MemAccess.semAcc_release (a : MemAccess) (acc : Acc) (h : acc.release = false) :
    (a.semAcc acc).release = true ↔ a.sem = .release ∨ a.sem = .acqRel := by
  cases hs : a.sem <;> simp [MemAccess.semAcc, hs, h]

/-- An access with weak memory semantics located by `accessLoc`, or a `st.bulk`, is a weak
access. A strong access located by `accessLoc` keeps its memory semantics in its footprint
(`MemAccess.semAcc`), so a `.read` template of an `.acquire` or `.acq_rel` load and a `.write`
template of a `.release` or `.acq_rel` store are no weak access. -/
theorem accessTmpl_isWeakMem {a : MemAccess} (hsem : a.sem = .weak) :
    (accessTmpl A L g t a).IsWeakMem := by
  unfold accessTmpl bulkInitTmpl
  dsimp only
  repeat' split
  all_goals first
    | trivial
    | exact (accessAcc_weak ‹_› hsem).1
    | exact (accessAcc_weak ‹_› hsem).2.1

/-- A `st.bulk` is a write or undefined behaviour. -/
theorem bulkInitTmpl_isMem {a : MemAccess} : (bulkInitTmpl L g t a).IsMem := by
  unfold bulkInitTmpl
  dsimp only
  split <;> trivial

/-- An atomic read-modify-write is a read-modify-write or undefined behaviour. -/
theorem atomTmpl_isMem {a : MemAccess} : (atomTmpl A L g t a).IsMem := by
  unfold atomTmpl
  dsimp only
  repeat' split <;> trivial

/-- An access located by `accessLoc`, or a `st.bulk`, is a read, a non-coherent read, a write or
undefined behaviour. -/
theorem accessTmpl_isMem {a : MemAccess} : (accessTmpl A L g t a).IsMem := by
  unfold accessTmpl
  dsimp only
  split
  · exact bulkInitTmpl_isMem
  all_goals repeat' first | trivial | split

/-- Every memory access is a read, a non-coherent read, a write, an atomic read-modify-write or
undefined behaviour. -/
theorem memTmpl_isMem {a : MemAccess} : (memTmpl A L g t a).IsMem := by
  unfold memTmpl
  split
  · split
    · exact acquireLoadTmpl_isMem
    · exact loadTmpl_isMem
    · exact releaseStoreTmpl_isMem
    · exact storeTmpl_isMem
    · exact accessTmpl_isMem
  · exact atomTmpl_isMem
  · split
    · exact accessTmpl_isMem
    · trivial


/-- A memory access that `memTmpl` locates with `accessLoc`: its location is not fixed by the
instruction (a generic address, a `.shared::cluster` window, an extension or a cache hint). -/
def dynamicAccess : Op → Bool
  | .mem a => match a.rule, a.locSpace?, a.addr.base with
    | some .threadAccess, some _, .reg _ _ => false
    | r, _, _ => r == some .threadAccess
  | _ => false

/-- An access `memTmpl` sends to `accessTmpl` is a dynamic access. -/
theorem dynamicAccess_of {a : MemAccess} (hr : a.rule = some .threadAccess)
    (hn : ∀ sp base w, a.locSpace? = some sp → a.addr.base = .reg base w → False) :
    dynamicAccess (.mem a) = true := by
  simp only [dynamicAccess]
  split
  · rename_i hs hb; exact absurd (hn _ _ _ hs hb) id
  · simp_all

/-- `dynamicAccess_of` with the rule premise inside the location premise. -/
theorem dynamicAccess_of' {a : MemAccess} (hr : a.rule = some .threadAccess)
    (hn : ∀ sp base w, a.rule = some .threadAccess → a.locSpace? = some sp →
      a.addr.base = .reg base w → False) :
    dynamicAccess (.mem a) = true :=
  dynamicAccess_of hr fun sp base w h1 h2 => hn sp base w hr h1 h2

/-- After a load without extension, `afterAccessLoad` is `afterLoad`. -/
theorem afterAccessLoad_same {w : Nat} {ds : List Nat} :
    afterAccessLoad t .same w ds = afterLoad t ds := by
  funext bs
  unfold afterAccessLoad afterLoad
  cases rebuild 3 bs <;> rfl

/-- A load located by `accessLoc` is a read, a non-coherent read or undefined behaviour; without
`.nc` it is a read continuing with `afterAccessLoad`, whose footprint acquires when the access has
`.acquire` or `.acq_rel` semantics (`MemAccess.semAcc`). -/
theorem accessTmpl_load {a : MemAccess} (hk : a.kind = .load) :
    (∃ f, accessTmpl A L g t a = .ub f) ∨
      (∃ acc, a.nc = false ∧ (acc.acquire = true ↔ a.sem = .acquire ∨ a.sem = .acqRel) ∧
        accessTmpl A L g t a = .read acc (afterAccessLoad t a.ext a.elem.width a.regs)) ∨
      ∃ acc k, a.nc = true ∧ accessTmpl A L g t a = .readNC acc k := by
  unfold accessTmpl
  simp only [hk]
  split
  · exact .inl ⟨_, rfl⟩
  · rename_i acc hacc
    split
    · split
      · exact .inr (.inr ⟨_, _, by simp_all, rfl⟩)
      · exact .inl ⟨_, rfl⟩
    · obtain ⟨acc0, he, h1, -, -⟩ := accessAcc_semAcc hacc
      have hq : acc.acquire = true ↔ a.sem = .acquire ∨ a.sem = .acqRel := by
        rw [← he]; exact MemAccess.semAcc_acquire a acc0 h1
      exact .inr (.inl ⟨_, by simp_all, hq, rfl⟩)

/-- An access located by `accessLoc` that is not a load is a write or undefined behaviour. -/
theorem accessTmpl_write {a : MemAccess} (hk : a.kind ≠ .load) :
    (∃ f, accessTmpl A L g t a = .ub f) ∨ ∃ acc bs u, accessTmpl A L g t a = .write acc bs u := by
  unfold accessTmpl bulkInitTmpl
  dsimp only
  split
  · split
    · exact .inl ⟨_, rfl⟩
    · exact .inr ⟨_, _, _, rfl⟩
  · exact absurd ‹_› hk
  · repeat' split
    all_goals first | exact .inl ⟨_, rfl⟩ | exact .inr ⟨_, _, _, rfl⟩
  · exact .inl ⟨_, rfl⟩

/-- A store located by `accessLoc` is a write continuing with `afterStore`, or undefined
behaviour; its footprint releases when the access has `.release` or `.acq_rel` semantics
(`MemAccess.semAcc`). -/
theorem accessTmpl_store {a : MemAccess} (hk : a.kind = .store) :
    (∃ f, accessTmpl A L g t a = .ub f) ∨ ∃ acc bs,
      (acc.release = true ↔ a.sem = .release ∨ a.sem = .acqRel) ∧
      accessTmpl A L g t a = .write acc bs (afterStore t a.srcs) := by
  unfold accessTmpl
  simp only [hk]
  split
  · exact .inl ⟨_, rfl⟩
  · rename_i acc hacc
    repeat' split
    all_goals first
      | exact .inl ⟨_, rfl⟩
      | (obtain ⟨acc0, he, -, h2, -⟩ := accessAcc_semAcc hacc
         have hq : acc.release = true ↔ a.sem = .release ∨ a.sem = .acqRel := by
           rw [← he]; exact MemAccess.semAcc_release a acc0 h2
         exact .inr ⟨_, _, hq, rfl⟩)

variable {a : MemAccess} {sp : Space} {base w : Nat}

/-- A weak load under THREAD-ACCESS is `loadTmpl`. -/
theorem memTmpl_load (hr : a.rule = some .threadAccess) (hs : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base w) (hk : a.kind = .load) (hsem : a.sem = .weak) :
    memTmpl A L g t a = loadTmpl A L g t sp a.nc a.elem.width a.regs base a.addr.off := by
  unfold memTmpl
  rw [hr, hs, hb]
  split <;> simp_all

/-- An acquire load into one register under THREAD-ACCESS is `acquireLoadTmpl`. -/
theorem memTmpl_acquire {d : Nat} (hr : a.rule = some .threadAccess)
    (hs : a.locSpace? = some sp) (hb : a.addr.base = .reg base w) (hk : a.kind = .load)
    (hsem : a.sem = .acquire) (hd : a.regs = [d]) :
    memTmpl A L g t a =
      acquireLoadTmpl A L g t (a.scope.getD .cta) sp a.elem.width d base a.addr.off := by
  unfold memTmpl
  rw [hr, hs, hb]
  split <;> simp_all

/-- A weak store under THREAD-ACCESS is `storeTmpl`. -/
theorem memTmpl_store (hr : a.rule = some .threadAccess) (hs : a.locSpace? = some sp)
    (hb : a.addr.base = .reg base w) (hk : a.kind = .store) (hsem : a.sem = .weak) :
    memTmpl A L g t a = storeTmpl L g t sp a.elem.width base a.addr.off a.srcs := by
  unfold memTmpl
  rw [hr, hs, hb]
  split <;> simp_all

/-- A release store of one value under THREAD-ACCESS is `releaseStoreTmpl`. -/
theorem memTmpl_release {v : Opnd} (hr : a.rule = some .threadAccess)
    (hs : a.locSpace? = some sp) (hb : a.addr.base = .reg base w) (hk : a.kind = .store)
    (hsem : a.sem = .release) (hv : a.srcs = [v]) :
    memTmpl A L g t a =
      releaseStoreTmpl L g t (a.scope.getD .cta) sp a.elem.width base a.addr.off v := by
  unfold memTmpl
  rw [hr, hs, hb]
  split <;> simp_all

end Mem

/-- A shuffle is `shflTmpl` when THREAD-SHFL is its rule and `noRule` otherwise. -/
theorem warpTmpl_shfl {mode : ShflMode} {ty : Option DType} {d : Nat} {ps : List (Option Nat)}
    {a b c mask : Opnd} :
    warpTmpl L g t ⟨.shfl mode, ty, some d :: ps, [a, b, c], some mask⟩ =
      shflTmpl L g t mode d ps.head?.join a b c mask ∨
    warpTmpl L g t ⟨.shfl mode, ty, some d :: ps, [a, b, c], some mask⟩ = .ub .noRule := by
  unfold warpTmpl
  cases h : WarpInstr.rule ⟨.shfl mode, ty, some d :: ps, [a, b, c], some mask⟩ with
  | none => exact .inr rfl
  | some r => cases r <;> simp

/-- `shfl.sync.idx.b32 d|p, a, b, c, mask` with a validity predicate is `shflTmpl`. -/
theorem warpTmpl_shfl_idx {ty : Option DType} {d p : Nat} {a b c mask : Opnd} :
    warpTmpl L g t ⟨.shfl .idx, ty, [some d, some p], [a, b, c], some mask⟩ =
      shflTmpl L g t .idx d (some p) a b c mask := rfl

/-- `vote.sync.ballot.b32` is `voteTmpl`. -/
theorem warpTmpl_vote {neg : Bool} {ty : Option DType} {d a : Nat} {mask : Opnd} :
    warpTmpl L g t ⟨.vote .ballot neg, ty, [some d], [.reg a], some mask⟩ =
      voteTmpl L g t d a neg mask := rfl

/-- `elect.sync` is `electTmpl`. -/
theorem warpTmpl_elect {ty : Option DType} {d : Option Nat} {p : Nat} {mask : Opnd} :
    warpTmpl L g t ⟨.elect, ty, [d, some p], [], some mask⟩ = electTmpl L g t d p mask := rfl

/-- `bar.warp.sync` is `warpBarTmpl`. -/
theorem warpTmpl_barWarp {ty : Option DType} {mask : Opnd} :
    warpTmpl L g t ⟨.barWarp, ty, [], [], some mask⟩ = warpBarTmpl L g t mask := rfl

/-- The shapes of a warp template: a shuffle, a vote, a reduction, a match, an `activemask`, an
election, a warp barrier or undefined behaviour. -/
def Tmpl.IsWarp : Tmpl → Prop
  | .shfl .. | .vote .. | .voteMode .. | .redux .. | .match_ .. | .activemask _ | .elect ..
  | .warpBar .. | .ub _ => True
  | _ => False

/-- Every warp collective is a shuffle, a vote, a reduction, a match, an `activemask`, an
election, a warp barrier or undefined behaviour. -/
theorem warpTmpl_isWarp {w : WarpInstr} : (warpTmpl L g t w).IsWarp := by
  unfold warpTmpl
  split
  · unfold shflTmpl; repeat' first | trivial | split
  · unfold voteTmpl; repeat' first | trivial | split
  · unfold voteModeTmpl; repeat' first | trivial | split
  · unfold reduxTmpl; repeat' first | trivial | split
  · unfold matchTmpl; repeat' first | trivial | split
  · trivial
  · unfold electTmpl; repeat' first | trivial | split
  · unfold warpBarTmpl; repeat' first | trivial | split
  · trivial

end PTX
