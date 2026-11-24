-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.PlainExtend
public import Lemmas.Step.Issue
public import Lemmas.Isa.Tmpl

@[expose] public section

/-! # The next event of a thread without asynchronous instructions

A thread of a kernel without asynchronous and shuffle instructions (`Kernel.NoTma`,
`Kernel.NoShfl`, both checked by `rfl`) performs only reads without acquire semantics,
non-coherent reads, writes without release semantics, CTA barriers, its exit and undefined
behaviour (`out_plain`). In an execution without asynchronous events (`Execution.NoTma`) a thread
whose last event is no barrier that is not ready (`hbl`) is released (`Execution.NoTma.released`),
and each of these events extends the execution by a counted event
(`Execution.NoTma.next_extends`): a read takes its bytes from causally maximal visible writes or
the launch memory, every other event needs nothing. A barrier is appended after the thread's
first event. The kernel's assumptions must hold of the extensions built (`hwf`): a non-coherent
read returns the launch content of the bytes it reads (`Execution.launchBytes`). -/

namespace PTX

noncomputable section

/-- Whether a template is a shuffle. -/
def Tmpl.isShfl : Tmpl → Bool
  | .shfl .. => true
  | _ => false

/-- Whether an instruction is a shuffle. -/
def Op.isShfl : Op → Bool
  | .warp ⟨.shfl _, _, _, _, _⟩ => true
  | _ => false

/-- Whether a template is a CTA barrier. -/
def Tmpl.isBar : Tmpl → Bool
  | .bar .. => true
  | _ => false

/-- Whether an instruction is a CTA barrier. -/
def Op.isBar : Op → Bool
  | .barSync .. | .barSyncN .. => true
  | _ => false

/-- No instruction of `K` is a shuffle; checked by `rfl`. -/
def Kernel.NoShfl (K : Kernel) : Prop := K.code.all (fun ins => !ins.op.isShfl) = true

/-- Whether an instruction is an atomic read-modify-write (`atom`, `red`; THREAD-ATOMIC). -/
def Op.isAtomic : Op → Bool
  | .mem a => a.rule == some .threadAtomic
  | _ => false

/-- No instruction of `K` is an atomic read-modify-write; checked by `rfl`. -/
def Kernel.NoAtomic (K : Kernel) : Prop := K.code.all (fun ins => !ins.op.isAtomic) = true

/-- Whether a template is an atomic read-modify-write. -/
def Tmpl.isRmw : Tmpl → Bool
  | .rmw .. => true
  | _ => false

/-- A read of varying special registers bounds each value by a positive bound, so it can return
a value. -/
def Tmpl.SregBounded : Tmpl → Prop
  | .sreg reads _ => ∀ p ∈ reads, 0 < p.2
  | _ => True

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

/-- An instruction outside the asynchronous instructions and the shuffle performs no shuffle. -/
theorem eventTmpl_not_shfl {t : TState} {op : Op} (h : op.isTma = false)
    (hs : op.isShfl = false) : (eventTmpl A L g t op).isShfl = false := by
  cases op
  case mem a =>
    have hm := memTmpl_isMem (A := A) (L := L) (g := g) (t := t) (a := a)
    simp only [eventTmpl]
    generalize memTmpl A L g t a = m at hm ⊢
    cases m <;> first | rfl | exact hm.elim
  case warp w =>
    rcases w with ⟨⟨⟩, _, _, _, _⟩ <;> simp [Op.isTma, Op.isShfl] at h hs
  all_goals simp only [Op.isTma, Op.isLocal, Bool.not_true, Bool.not_false,
    Bool.true_eq_false] at h
  all_goals simp only [eventTmpl]
  all_goals first
    | rfl
    | (unfold barTmpl; repeat' first | rfl | split)
    | (split <;> first | rfl | (rename_i r _; cases r <;> rfl))

/-- An instruction outside the asynchronous instructions and the barriers performs no barrier. -/
theorem eventTmpl_not_bar {t : TState} {op : Op} (h : op.isTma = false)
    (hb : op.isBar = false) : (eventTmpl A L g t op).isBar = false := by
  cases op
  case mem a =>
    have hm := memTmpl_isMem (A := A) (L := L) (g := g) (t := t) (a := a)
    simp only [eventTmpl]
    generalize memTmpl A L g t a = m at hm ⊢
    cases m <;> first | rfl | exact hm.elim
  case warp w =>
    have hm := warpTmpl_isWarp (L := L) (g := g) (t := t) (w := w)
    simp only [eventTmpl]
    generalize warpTmpl L g t w = m at hm ⊢
    cases m <;> first | rfl | exact hm.elim
  all_goals simp only [Op.isTma, Op.isLocal, Bool.not_true, Bool.not_false,
    Bool.true_eq_false] at h
  all_goals simp only [eventTmpl]
  all_goals first
    | rfl
    | (split <;> first | rfl | (rename_i r _; cases r <;> rfl))
    | (simp [Op.isBar] at hb)

/-- Every bound of a special-register read is positive. -/
theorem SReg.readBound_pos (s : SReg) : 0 < s.readBound L g := by
  unfold SReg.readBound
  split
  · dsimp only
    split
    · exact Nat.two_pow_pos _
    · exact Nat.lt_min.mpr ⟨Nat.two_pow_pos _, by omega⟩
  · exact Nat.two_pow_pos _

/-- The template of a memory access without read-modify-write: a read, a non-coherent read, a
write or undefined behaviour. -/
def Tmpl.IsPlainMem : Tmpl → Prop
  | .read .. | .readNC .. | .write .. | .ub _ => True
  | _ => False

theorem Tmpl.IsPlainMem.not_rmw {m : Tmpl} (h : m.IsPlainMem) : m.isRmw = false := by
  cases m <;> first | rfl | exact h.elim

theorem loadTmpl_isPlainMem {t : TState} {sp : Space} {nc : Bool} {w : Nat} {ds : List Nat}
    {base : Nat} {off : Int} : (loadTmpl A L g t sp nc w ds base off).IsPlainMem := by
  unfold loadTmpl; repeat' first | trivial | split

theorem storeTmpl_isPlainMem {t : TState} {sp : Space} {w base : Nat} {off : Int}
    {srcs : List Opnd} : (storeTmpl L g t sp w base off srcs).IsPlainMem := by
  unfold storeTmpl; repeat' first | trivial | split

theorem acquireLoadTmpl_isPlainMem {t : TState} {sc : MbarScope} {sp : Space} {w d base : Nat}
    {off : Int} : (acquireLoadTmpl A L g t sc sp w d base off).IsPlainMem := by
  have h := loadTmpl_isPlainMem (A := A) (L := L) (g := g) (t := t) (sp := sp) (nc := false)
    (w := w) (ds := [d]) (base := base) (off := off)
  unfold acquireLoadTmpl
  generalize loadTmpl A L g t sp false w [d] base off = m at h ⊢
  cases m <;> trivial

theorem releaseStoreTmpl_isPlainMem {t : TState} {sc : MbarScope} {sp : Space} {w base : Nat}
    {off : Int} {v : Opnd} : (releaseStoreTmpl L g t sc sp w base off v).IsPlainMem := by
  have h := storeTmpl_isPlainMem (L := L) (g := g) (t := t) (sp := sp) (w := w) (base := base)
    (off := off) (srcs := [v])
  unfold releaseStoreTmpl
  generalize storeTmpl L g t sp w base off [v] = m at h ⊢
  cases m <;> trivial

theorem accessTmpl_isPlainMem {t : TState} {a : MemAccess} :
    (accessTmpl A L g t a).IsPlainMem := by
  unfold accessTmpl
  dsimp only
  split
  · unfold bulkInitTmpl; dsimp only; split <;> trivial
  all_goals repeat' first | trivial | split

/-- A memory access that is no atomic performs no read-modify-write. -/
theorem memTmpl_isPlainMem {t : TState} {a : MemAccess} (ha : a.rule ≠ some .threadAtomic) :
    (memTmpl A L g t a).IsPlainMem := by
  unfold memTmpl
  split
  · split
    · exact acquireLoadTmpl_isPlainMem
    · exact loadTmpl_isPlainMem
    · exact releaseStoreTmpl_isPlainMem
    · exact storeTmpl_isPlainMem
    · exact accessTmpl_isPlainMem
  · rename_i hr; exact (ha hr).elim
  · split
    · exact accessTmpl_isPlainMem
    · trivial

/-- An instruction that is no atomic performs no atomic read-modify-write. -/
theorem eventTmpl_not_rmw {t : TState} {op : Op} (h : op.isTma = false)
    (ha : op.isAtomic = false) : (eventTmpl A L g t op).isRmw = false := by
  cases op
  case mem a =>
    simp only [Op.isAtomic, beq_eq_false_iff_ne, ne_eq] at ha
    exact (memTmpl_isPlainMem ha).not_rmw
  case warp w =>
    have hm := warpTmpl_isWarp (L := L) (g := g) (t := t) (w := w)
    simp only [eventTmpl]
    generalize warpTmpl L g t w = m at hm ⊢
    cases m <;> first | rfl | exact hm.elim
  all_goals simp only [Op.isTma, Op.isLocal, Bool.not_true, Bool.not_false,
    Bool.true_eq_false] at h
  all_goals simp only [eventTmpl]
  all_goals first
    | rfl
    | (unfold barTmpl; repeat' first | rfl | split)
    | (split <;> first | rfl | (rename_i r _; cases r <;> rfl))

theorem sreg_reads_pos {ss : List SReg} :
    ∀ p ∈ ss.map (fun s => (s, s.readBound L g)), 0 < p.2 := by
  intro p hp
  obtain ⟨s, -, rfl⟩ := List.mem_map.mp hp
  exact SReg.readBound_pos s

/-- The special-register reads of an instruction have positive bounds. -/
theorem eventTmpl_sregBounded {t : TState} {op : Op} (h : op.isTma = false) :
    (eventTmpl A L g t op).SregBounded := by
  cases op
  case mem a =>
    have hm := memTmpl_isMem (A := A) (L := L) (g := g) (t := t) (a := a)
    simp only [eventTmpl]
    generalize memTmpl A L g t a = m at hm ⊢
    cases m <;> trivial
  case warp w =>
    have hm := warpTmpl_isWarp (L := L) (g := g) (t := t) (w := w)
    simp only [eventTmpl]
    generalize warpTmpl L g t w = m at hm ⊢
    cases m <;> trivial
  all_goals simp only [Op.isTma, Op.isLocal, Bool.not_true, Bool.not_false,
    Bool.true_eq_false] at h
  all_goals simp only [eventTmpl]
  all_goals first
    | trivial
    | (unfold barTmpl; repeat' first | trivial | split)
    | (split
       · rename_i r _
         cases r <;> simp only [localSregTmpl, sregTmpl, Tmpl.SregBounded] <;>
           exact sreg_reads_pos
       · trivial)

/-- **The templates of a plain kernel**: neither asynchronous, a shuffle nor an atomic
read-modify-write, and every special-register read has positive bounds. -/
theorem out_plain (hK : K.NoTma) (hS : K.NoShfl) (hR : K.NoAtomic) {t : TState} {m : Tmpl}
    (h : out K A L g t = .ev m) :
    m.isTma = false ∧ m.isShfl = false ∧ m.isRmw = false ∧ m.SregBounded := by
  refine ⟨out_noTma hK h, ?_⟩
  unfold out at h
  split at h
  · cases h; exact ⟨rfl, rfl, trivial⟩
  · split at h
    · cases h; exact ⟨rfl, rfl, trivial⟩
    · rename_i ins hins
      split at h
      · cases h; exact ⟨rfl, rfl, trivial⟩
      · cases h
      · split at h
        · split at h
          · cases h
          · cases h; exact ⟨rfl, rfl, trivial⟩
        · cases h
          have h1 := List.all_eq_true.mp hK ins (List.mem_of_getElem? hins)
          have h2 := List.all_eq_true.mp hS ins (List.mem_of_getElem? hins)
          have h3 := List.all_eq_true.mp hR ins (List.mem_of_getElem? hins)
          simp only [Bool.not_eq_true'] at h1 h2 h3
          exact ⟨eventTmpl_not_shfl h1 h2, eventTmpl_not_rmw h1 h3, eventTmpl_sregBounded h1⟩

/-- The bytes a non-coherent read of `a` returns: the launch content of each allocated byte. -/
def Execution.launchBytes (X : Execution) (mem0 : Mem0) (a : Acc) : List (Option Byte) :=
  (List.range a.size).map fun k =>
    (mem0 (a.loc.at k)).elim none fun c => X.initialByte c (a.loc.at k)

/-- The extension of `X` by an event of the thread `g`: the assumptions' condition for each event
that is not a non-coherent read of other bytes than the launch content. -/
def Execution.ExtWf (A : List Assumption) (L : Launch) (mem0 : Mem0) (X : Execution)
    (g : Nat) : Prop :=
  ∀ e r, (∀ a bs, e.kind = .nc a bs → bs.length = a.size ∧ ∀ k < a.size, ∀ c,
      mem0 (a.loc.at k) = some c → bs[k]? = some (X.initialByte c (a.loc.at k))) →
    ∀ a ∈ A, a.wf L mem0 (X.snoc g e r)

namespace Execution.NoTma

variable {mem0 : Mem0} {X : Execution}

/-- **A thread whose last event is no barrier that is not ready is released**: without
asynchronous events the only blocking event that is not a warp collective is a `bar.sync`. -/
theorem released (hn : X.NoTma)
    (hbl : ∀ id count pc, X.IsBarrier (g, (X.tr g).length - 1) id count pc →
      Ready L X (g, (X.tr g).length - 1)) :
    Step.Released L X g := by
  refine ⟨fun pc k hq hk => ?_⟩
  have ht := hn _ _ _ hq
  cases k
  case bar id count mode =>
    cases mode
    · exact hbl id count pc hq
    · simp [Kind.isTma] at ht
  case tc t => cases t <;> simp [Kind.isTma] at ht
  all_goals simp [Kind.resume, Kind.isTma] at hk ht

/-- **The next event of a thread without asynchronous instructions extends the execution** by a
counted event, given that its last event is no barrier that is not ready, that the event is no
atomic read-modify-write, and that its special-register reads have positive bounds. -/
theorem next_extends (hX : Consistent L K A mem0 X) (hn : X.NoTma) (hg : g < L.threads)
    {t t1 : TState} (hrun : Run K A L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau K A L g) t t1) {m : Tmpl}
    (hout : out K A L g t1 = .ev m) (hm : m.isTma = false) (hs : m.isShfl = false)
    (hrmw : m.isRmw = false) (hsr : m.SregBounded)
    (hbne : ∀ id u c, m = .bar id u c → X.tr g ≠ [])
    (hbl : ∀ id count pc, X.IsBarrier (g, (X.tr g).length - 1) id count pc →
      Ready L X (g, (X.tr g).length - 1))
    (hwf : X.ExtWf A L mem0 g) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have simple : ∀ {e : Event} {o : Option TState}, EStep K A L g t1 e o → e.kind.isTma = false →
      (∀ id count mode, e.kind ≠ .bar id count mode) → (∀ md a b c recv ok,
          e.kind ≠ .shfl md a b c recv ok) →
      (∀ a bs, e.kind ≠ .rd a bs) → (∀ a old new, e.kind ≠ .rmw a old new) → e.counts = true →
      (∀ a bs, e.kind = .nc a bs → bs.length = a.size ∧ ∀ k < a.size, ∀ c,
        mem0 (a.loc.at k) = some c → bs[k]? = some (X.initialByte c (a.loc.at k))) →
      ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
    intro e o he hk hnb hns hnr hnrmw hc hnc
    refine ⟨_, simple_extend hX hn hg hrun hl he hk hnb hns hnr hnrmw (released hn hbl).ready
      (hwf e _ hnc),
      le_snoc, ?_⟩
    rw [size_snoc hX hg hc]
    omega
  cases m with
  | read a k =>
    obtain ⟨bs, r, hY⟩ := read_extend hX hn hg hrun hl hout hm (released hn hbl).ready
      (fun _ _ => hwf _ _ nofun)
    refine ⟨_, hY, le_snoc, ?_⟩
    rw [size_snoc hX hg rfl]
    omega
  | readNC a k =>
    refine simple (e := ⟨t1.pc, .nc a (X.launchBytes mem0 a)⟩)
      ⟨_, hout, _, by simp [Execution.launchBytes], rfl, rfl⟩ rfl nofun nofun nofun nofun rfl ?_
    intro a' bs h
    simp only [Kind.nc.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by simp [Execution.launchBytes], fun k hk c hc => ?_⟩
    simp [Execution.launchBytes, List.getElem?_range hk, hc]
  | write a bs u =>
    exact simple (e := ⟨t1.pc, .wr a bs⟩) ⟨_, hout, rfl, rfl⟩ hm nofun nofun nofun nofun rfl nofun
  | exit =>
    exact simple (e := ⟨t1.pc, .exit⟩) (o := none) ⟨_, hout, rfl, rfl⟩ rfl nofun nofun nofun nofun
      rfl nofun
  | ub f =>
    exact simple (e := ⟨t1.pc, .ub f⟩) (o := none) ⟨_, hout, rfl, rfl⟩ rfl nofun nofun nofun nofun
      rfl nofun
  | bar id u c mode =>
    cases mode
    · exact Step.bar_counted_extension hX hg (.inl (hbne id u c rfl)) (released hn hbl)
        (hwf _ _ nofun) hrun hl ⟨_, hout, rfl, rfl⟩
    · cases hm
  | shfl => cases hs
  | rmw a f k => cases hrmw
  | sreg reads k =>
    refine simple (e := ⟨t1.pc, .sreg (reads.map Prod.fst) (reads.map fun _ => 0)⟩)
      ⟨_, hout, _, ?_, rfl, rfl⟩ rfl nofun nofun nofun nofun rfl nofun
    rw [List.forall₂_map_left_iff]
    exact List.forall₂_same.mpr hsr
  | _ => cases hm

end Execution.NoTma

end

end PTX
