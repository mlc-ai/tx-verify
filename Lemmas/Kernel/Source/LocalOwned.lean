-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Source.Local
public import Lemmas.Flow.WriteSpace
public import Lemmas.Flow.NotRmw
public import Lemmas.Flow.NotBulk
public import Lemmas.Flow.NotTensor
public import Lemmas.Protocol.Region

@[expose] public section

/-! # Local memory is written only by its owner thread, in every consistent execution

A proof tool, generic over the kernel. `LocalOwned X` (every write of a `.local` location is an
event of the location's owner thread, `Lemmas/Kernel/Source/Local.lean`) holds in every
consistent execution of every kernel (`localOwned`), so a kernel need not pass it to the local
read source.

* **Thread writes.** A store or an atomic read-modify-write locates its bytes by `accessLoc`, whose
  `.local` locations are the thread's own (`accessLoc_local_owner`); a store with a direct
  address (`storeTmpl`) has no rule in local memory (`effAddr` of `.local` fails); a `movmatrix`
  store and a Tensor Memory allocation's address store write shared memory
  (`fires_write_local_owner`, `fires_rmw_local_owner`).
* **Asynchronous writes.** Core's issue templates give every asynchronous write a shared or global
  destination: a linear copy's (`cp.async`, `cp.async.bulk`, `st.async`/`red.async`) from
  `effAddr` of a shared or global space, `sharedEffAddr` or a location checked to be shared or
  global (`fires_copy_dst`); a tensor load's tile from its shared base (`fires_tensorIssue_base`);
  a tensor store's bytes in global memory (`store_writeLoc_global`); a CLC response at its shared
  buffer (`fires_clcIssue_response`). -/

namespace PTX.Flow
open PTX

noncomputable section

variable {A : List Assumption} {L : Launch} {g : Nat} {t : TState}

/-! ### Thread writes -/

/-- An effective address is in a shared or the global space. -/
theorem effAddr_not_local {sp : Space} {base : Nat} {off : Int} {loc : Loc}
    (h : effAddr L g t sp base off = .ok loc) : loc.space ≠ .local := by
  rw [effAddr_space h]
  cases sp with
  | global => decide
  | shared => decide
  | «local» | const => cases h

/-- **The footprint `accessAcc` finds in local memory is the thread's own.** -/
theorem accessAcc_local_owner {a : MemAccess} {acc : Acc} (h : accessAcc L g t a = .ok acc)
    (hl : acc.loc.space = .local) : acc.loc.cta = g := by
  have hmap : ∀ {α : Type} {f : α → Acc} {x : Exec α} {r : Acc}, f <$> x = .ok r →
      ∃ y, x = .ok y ∧ f y = r := by
    intro α f x r hx
    cases x with
    | error e => simp at hx
    | ok y => exact ⟨y, rfl, by simpa using hx⟩
  unfold accessAcc at h
  simp only [bind, Except.bind] at h
  cases hloc : accessLoc L g t a with
  | error f => simp only [hloc, reduceCtorEq] at h
  | ok loc =>
    simp only [hloc] at h
    repeat' (first | split at h | contradiction)
    obtain ⟨acc0, h0, he⟩ := hmap h
    obtain ⟨h1, h2⟩ := elemAcc_local h0
    subst he
    rw [semAcc_loc] at hl ⊢
    rw [h2]
    exact Frame.accessLoc_local_owner hloc (h1 ▸ hl)

/-- A store with a direct address writes no local memory. -/
theorem storeTmpl_not_local {sp : Space} {w base : Nat} {off : Int} {srcs : List Opnd} {a : Acc}
    {bs : List Byte} {u : TState} (h : storeTmpl L g t sp w base off srcs = .write a bs u) :
    a.loc.space ≠ .local := by
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
        exact effAddr_not_local hloc

/-- A strong or extended access writes the thread's own local memory, if local. -/
theorem accessTmpl_local_owner {ma : MemAccess} {a : Acc} {bs : List Byte} {u : TState}
    (h : accessTmpl A L g t ma = .write a bs u) (hl : a.loc.space = .local) : a.loc.cta = g := by
  unfold accessTmpl at h
  split at h
  · -- `st.bulk`: a location of `accessLoc`
    unfold bulkInitTmpl at h
    dsimp only at h
    split at h
    · cases h
    · rename_i loc n hr
      simp only [Tmpl.write.injEq] at h
      obtain ⟨rfl, -, -⟩ := h
      simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw] at hr
      cases hloc : accessLoc L g t ma with
      | error f => simp only [hloc] at hr; cases hr
      | ok l =>
        simp only [hloc] at hr
        repeat' (first | split at hr | (cases hr; done))
        all_goals
          simp only [Except.ok.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, -⟩ := hr
          exact Frame.accessLoc_local_owner hloc hl
  · repeat' (first | split at h | cases h)
  · split at h
    · cases h
    · rename_i acc hacc
      split at h
      · cases h
      · dsimp only at h
        split at h
        · cases h
        · simp only [Tmpl.write.injEq] at h
          obtain ⟨rfl, -, -⟩ := h
          exact accessAcc_local_owner hacc hl
  · cases h

/-- **A thread's write event in local memory is in its own local memory.** -/
theorem fires_write_local_owner {op : Op} {pc epc : Nat} {a : Acc} {bs : List Byte}
    {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) ⟨epc, .wr a bs⟩ o)
    (hl : a.loc.space = .local) : a.loc.cta = g := by
  have hop := fires_write_op hf rfl
  rcases fires_write_tmpl hf with ⟨u, hm⟩ | ⟨u, hm, -⟩
  swap
  · exfalso
    cases op
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
      rw [← hloc, effAddr_space (by assumption)] at hl
      cases hl
  cases op <;> simp only [writeOp, Bool.false_eq_true] at hop
  case mem m =>
    simp only [eventTmpl, memTmpl] at hm
    split at hm
    · split at hm
      · have hk : m.kind = .load := by assumption
        simp [hk] at hop
      · have hk : m.kind = .load := by assumption
        simp [hk] at hop
      · simp only [releaseStoreTmpl] at hm
        split at hm
        · rename_i a0 bs0 t0 h0
          simp only [Tmpl.write.injEq] at hm
          obtain ⟨rfl, -, -⟩ := hm
          exact (storeTmpl_not_local h0 hl).elim
        · rename_i hne
          exact absurd hm (hne a bs u)
      · exact (storeTmpl_not_local hm hl).elim
      · exact accessTmpl_local_owner hm hl
    · exact absurd hm atomTmpl_noWrite
    · split at hm
      · exact accessTmpl_local_owner hm hl
      · cases hm
  case matrix m =>
    have hsp := matrixTmpl_write_spec hm
    rw [hsp.1] at hl
    cases hl
  case tcAlloc group base off nc =>
    simp only [eventTmpl, tcTmpl, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hm
    repeat' (first | split at hm | simp [ofExec] at hm)

theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- **A thread's atomic read-modify-write is in its own memory**: an `atom` or `red` locates its
element by `accessLoc`. -/
theorem fires_rmw_local_owner {op : Op} {pc epc : Nat} {a : Acc} {old : List (Option Byte)}
    {new : Option (List Byte)} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t op) ⟨epc, .rmw a old new⟩ o) (hl : a.loc.space = .local) :
    a.loc.cta = g := by
  have hop := fires_rmw_op hf rfl
  cases op <;> simp only [atomicOp, Bool.false_eq_true] at hop
  case mem m =>
    have hr : m.rule = some .threadAtomic := of_decide_eq_true hop
    simp only [eventTmpl, memTmpl_atomic hr] at hf
    unfold atomTmpl at hf
    dsimp only at hf
    split at hf
    · simp [Fires] at hf
    · rename_i op' acc vs hr'
      simp only [Fires] at hf
      obtain ⟨old', -, he, -⟩ := hf
      simp only [Event.mk.injEq, Kind.rmw.injEq] at he
      obtain ⟨-, rfl, -, -⟩ := he
      split at hr'
      · rename_i op0 _
        obtain ⟨loc, hloc, hr2⟩ := bind_ok hr'
        have hne : ∀ {α : Type} {f : Unit → Exec α} {x : α} {e : Fault},
            ((throw e : Exec Unit) >>= f) ≠ .ok x := by
          intro α f x e h; cases h
        by_cases h1 : loc.space = .global ∨ loc.space = .shared
        · rw [ite_eq_left h1] at hr2
          by_cases h2 : ((m.hints.policy.isSome || m.vec != 1) && loc.space != .global) = true
          · rw [ite_eq_left h2] at hr2
            exact absurd hr2 hne
          · rw [ite_eq_right h2] at hr2
            obtain ⟨acc0, hacc, hr3⟩ := bind_ok hr2
            obtain ⟨vs0, -, hr4⟩ := bind_ok hr3
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr4
            obtain ⟨-, rfl, -⟩ := hr4
            obtain ⟨h3, h4⟩ := elemAcc_local hacc
            simp only [atomAcc] at hl ⊢
            rw [h4]
            exact Frame.accessLoc_local_owner hloc (h3 ▸ hl)
        · rw [ite_eq_right h1] at hr2
          exact absurd hr2 hne
      · cases hr'


/-! ### Asynchronous writes -/

theorem ofExec_eq_ok {r : Exec Tmpl} {m : Tmpl} (hm : ∀ f, m ≠ .ub f) (h : ofExec r = m) :
    r = .ok m := by
  cases r with
  | error f => exact absurd h.symm (hm f)
  | ok m' => exact congrArg _ h

/-- The template of a copy event. -/
theorem fires_copy_tmpl {pc epc : Nat} {m : Tmpl} {s : AsyncCopy.Spec} {o : Option TState}
    (hf : Fires pc m ⟨epc, .copy s⟩ o) : ∃ u, m = .copy s u := by
  cases m <;> simp only [Fires] at hf <;> aesop

/-- The location of an `st.async` or `red.async` is checked to be shared or global. -/
theorem asyncStoreLoc_not_local {sp : Option StateSpace} {sh : Bool} {a : Addr} {l : Loc}
    (h : asyncStoreLoc L g t sp sh a = .ok l) : l.space ≠ .local := by
  unfold asyncStoreLoc at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' (first | split at h | (cases h; done))
  all_goals
    simp only [Except.ok.injEq] at h
    subst h
    intro hl
    simp_all

/-- **A linear copy's destination is in shared or global memory**: `cp.async` writes shared
memory at `effAddr`, `cp.async.bulk` shared memory at `effAddr` or `sharedEffAddr` (a peer CTA's
for a multicast) or global memory at `effAddr`, `st.async` and `red.async` a location checked to
be shared or global. -/
theorem fires_copy_dst {op : Op} {pc epc : Nat} {s : AsyncCopy.Spec} {o : Option TState}
    (hf : Fires pc (eventTmpl A L g t op) ⟨epc, .copy s⟩ o) : s.dst.loc.space ≠ .local := by
  have hop := fires_bulk_op hf rfl
  obtain ⟨u, hm⟩ := fires_copy_tmpl hf
  cases op <;> simp only [bulkOp, Bool.false_eq_true] at hop
  case cpBulk c =>
    simp only [eventTmpl, widenMbarScope] at hm
    have hm' : tmaTmpl L g t (.cpBulk c) = .copy s u := by
      split at hm
      · split at hm <;> first | cases hm | exact hm
      · exact hm
    simp only [tmaTmpl] at hm'
    have hr := ofExec_eq_ok (fun f h => by cases h) hm'
    unfold bulkCopyTmpl at hr
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw, bulkMulticast] at hr
    repeat' (first | split at hr | (cases hr; done))
    all_goals
      simp only [Except.ok.injEq, Tmpl.copy.injEq] at hr
      obtain ⟨rfl, -⟩ := hr
      dsimp only [bulkSpec]
      first
        | exact effAddr_not_local (by assumption)
        | exact fun h => by rw [sharedEffAddr_shared (by assumption)] at h; cases h
  case cpAsync db doff sb soff size source policy =>
    simp only [eventTmpl, cpAsyncTmpl] at hm
    have hr := ofExec_eq_ok (fun f h => by cases h) hm
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hr
    repeat' (first | split at hr | (cases hr; done))
    simp only [Except.ok.injEq, Tmpl.copy.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    exact effAddr_not_local (by assumption)
  case asyncStore st =>
    simp only [eventTmpl, asyncStoreTmpl] at hm
    have hr := ofExec_eq_ok (fun f h => by cases h) hm
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hr
    repeat' (first | split at hr | (cases hr; done))
    all_goals
      simp only [Except.ok.injEq, Tmpl.copy.injEq] at hr
      obtain ⟨rfl, -⟩ := hr
      exact asyncStoreLoc_not_local (by assumption)

/-- The elements of a linear copy are in its destination's space. -/
theorem copy_elem_space {s : AsyncCopy.Spec} {j : Nat} {a : Acc} (h : s.elems[j]? = some a) :
    a.loc.space = s.dst.loc.space := by
  simp only [AsyncCopy.Spec.elems, List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨k, -, rfl⟩ := h
  rfl

/-- **A tensor load writes the shared memory of its tile**: the issued copy's shared base passes
the route check (`TensorRoute`), which asks for shared memory, also for each multicast copy. -/
theorem fires_tensorIssue_base {op : Op} {pc epc a : Nat} {s : TensorCopy.Spec}
    {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) ⟨epc, .tensorIssue a s⟩ o) :
    s.sharedBase.space = .shared := by
  have hop : tensorOp op = true := by
    cases hq : tensorOp op
    · exact absurd rfl (fires_notTensor (eventTmpl_notTensor hq) hf a s)
    · rfl
  obtain ⟨u, hm⟩ : ∃ u, eventTmpl A L g t op = .tensorIssue a s u := by
    generalize eventTmpl A L g t op = m at hf
    cases m <;> simp only [Fires] at hf <;> aesop
  cases op <;> simp only [tensorOp, Bool.false_eq_true] at hop
  simp only [eventTmpl, tensorTmpl] at hm
  have hr := ofExec_eq_ok (fun f h => by cases h) hm
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
    tensorMulticast] at hr
  repeat' (first | split at hr | (cases hr; done))
  all_goals
    simp only [Except.ok.injEq, Tmpl.tensorIssue.injEq] at hr
    obtain ⟨-, rfl, -⟩ := hr
    exact (‹TensorRoute _ _ _ _ _ _›).2.1

/-- **A cancellation request's response buffer is in shared memory** (`effAddr` of `.shared`). -/
theorem fires_clcIssue_response {op : Op} {pc epc : Nat} {sp : Clc.Spec} {tg : List Nat}
    {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) ⟨epc, .clcIssue sp tg⟩ o) :
    sp.response.space = .shared := by
  have hop := fires_clcIssue_op hf rfl
  obtain ⟨u, hm⟩ : ∃ u, eventTmpl A L g t op = .clcIssue sp tg u := by
    generalize eventTmpl A L g t op = m at hf
    cases m <;> simp only [Fires] at hf <;> aesop
  cases op <;> simp only [clcOp, Bool.false_eq_true] at hop
  all_goals
    simp only [eventTmpl, clcTmpl] at hm
    have hr := ofExec_eq_ok (fun f h => by cases h) hm
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw] at hr
    repeat' (first | split at hr | (cases hr; done))
  all_goals
    simp only [Except.ok.injEq, Tmpl.clcIssue.injEq] at hr
    obtain ⟨rfl, -, -⟩ := hr
    exact effAddr_space (by assumption)

end

end PTX.Flow

namespace PTX.Frame
open PTX PTX.Flow

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **Local memory is written only by its owner thread**, in every consistent execution. -/
theorem localOwned (hX : Consistent L K A mem0 X) : LocalOwned X := by
  intro w a bs l hw hl hc
  obtain ⟨hsp, hcta, -⟩ := hc
  have hal : a.loc.space = .local := hsp ▸ hl
  have src : ∀ {i : EvId} {e : Event}, X.get i = some e → (∀ f, e.kind ≠ .ub f) →
      ∃ (t : TState) (ins : Instr) (o : Option TState),
        Fires e.pc (eventTmpl A L i.1 t ins.op) e o := by
    intro i e he hub
    rcases get_source hX he with ⟨f, hf⟩ | ⟨t, ins, o, -, -, hf⟩
    · exact absurd hf (hub f)
    · exact ⟨t, ins, o, hf⟩
  rcases w with i | ⟨i, part⟩
  · rcases hw with ⟨pc, he⟩ | ⟨old, pc, he⟩
    · obtain ⟨t, ins, o, hf⟩ := src he (fun f h => by cases h)
      have hown := fires_write_local_owner hf hal
      obtain ⟨g, j⟩ := i
      simp only at hown
      subst hown
      exact ⟨j, by rw [hcta], .inr (.inl ⟨bs, ⟨pc, by rw [hcta]; exact he⟩, rfl⟩)⟩
    · obtain ⟨t, ins, o, hf⟩ := src he (fun f h => by cases h)
      have hown := fires_rmw_local_owner hf hal
      obtain ⟨g, j⟩ := i
      simp only at hown
      subst hown
      exact ⟨j, by rw [hcta], .inr (.inr ⟨old, some bs, pc, by rw [hcta]; exact he⟩)⟩
  · exfalso
    cases part
    all_goals try exact hw.elim
    case writeCopy =>
      obtain ⟨sp, ⟨pc, he⟩, -, rfl, -⟩ := hw
      obtain ⟨t, ins, o, hf⟩ := src he (fun f h => by cases h)
      exact fires_copy_dst hf hal
    case writeElem j =>
      obtain ⟨sp, ⟨pc, he⟩, hel, -⟩ := hw
      obtain ⟨t, ins, o, hf⟩ := src he (fun f h => by cases h)
      exact fires_copy_dst hf (copy_elem_space hel ▸ hal)
    case writeLoad x y k =>
      obtain ⟨ob, addr, b, -, ⟨pc, he⟩, hloc, -⟩ := hw
      obtain ⟨t, ins, o, hf⟩ := src he (fun f h => by cases h)
      have hb := fires_tensorIssue_base hf
      simp only [TensorCopy.writeLoc, Option.map_eq_some_iff] at hloc
      obtain ⟨slot, -, hloc⟩ := hloc
      rw [← hloc] at hal
      simp only [TensorBox.sharedLoc] at hal
      rw [hb] at hal
      cases hal
    case writeStore x y k =>
      obtain ⟨ob, addr, b, -, -, hloc, -⟩ := hw
      rw [Execution.store_writeLoc_global hloc] at hal
      cases hal
    case writeCta c =>
      obtain ⟨sp, targets, ⟨pc, he⟩, -, -, r, -, rfl, -⟩ := hw
      obtain ⟨t, ins, o, hf⟩ := src he (fun f h => by cases h)
      have hr := fires_clcIssue_response hf
      simp only at hal
      rw [hr] at hal
      cases hal

/-- `local_read_byte_of_last_store` without the ownership premise (`localOwned`). -/
theorem local_read_byte (hX : Consistent L K A mem0 X)
    {g w e k : Nat} {a dst : Acc} {bs : List (Option Byte)} {written : List Byte}
    (hr : X.Reads (g, e) a bs) (hw : X.Writes (g, w) dst written) (hk : k < a.size)
    (hc : dst.Covers (a.loc.at k)) (hl : a.loc.space = .local) (hwe : w < e)
    (hlast : ∀ j d, X.Access (g, j) d true → d.Covers (a.loc.at k) → j ≤ w ∨ e < j) :
    bs[k]? = some (wbyte dst written (a.loc.at k)) :=
  local_read_byte_of_last_store hX (localOwned hX) hr hw hk hc hl hwe hlast

/-- `local_read_of_last_store` without the ownership premise (`localOwned`). -/
theorem local_read (hX : Consistent L K A mem0 X)
    {g w e : Nat} {a dst : Acc} {bs : List (Option Byte)} {written : List Byte}
    (hr : X.Reads (g, e) a bs) (hw : X.Writes (g, w) dst written) (hloc : dst.loc = a.loc)
    (hsize : dst.size = a.size) (hlen : written.length = a.size) (hl : a.loc.space = .local)
    (hwe : w < e)
    (hlast : ∀ j d, X.Access (g, j) d true → (∃ k < a.size, d.Covers (a.loc.at k)) →
      j ≤ w ∨ e < j) :
    bs = written.map some :=
  local_read_of_last_store hX (localOwned hX) hr hw hloc hsize hlen hl hwe hlast

end

end PTX.Frame
