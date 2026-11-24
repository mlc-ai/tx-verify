-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.PrologueEvents
public import Kernels.FlashAttn4Fwd.Proof.Thread.Machine
public import Lemmas.Flow.RunInv
public import Lemmas.Flow.Fire
public import Lemmas.Flow.ElectLead

@[expose] public section

/-! # The prologue's run invariant

Along a thread's run through the prologue (`Run`, one structure): every event is a shuffle, an
election, a barrier initialization, a fence of the initializations or a cluster-barrier
operation; every initialization is of a barrier of the thread's own CTA with its table count,
warp 0's of `FBar.ofInit j` for an index below the site's bound (initializations happen in index
order) and warp 12's of the handshake barrier; no barrier is initialized twice; every
initialization precedes the second fence; the fences and cluster-barrier operations so far are
those the site's position gives (`Site.fences`, `Site.clusters`). Every election has the full
member mask; at an initialization site an election returned the thread's lane (`Site.led`);
while every election returned the thread's lane, the thread initialized every barrier of its
warp the site has passed (`Done`). It is proved along the thread's machine (`run`, by
`Code.run_inv`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Prologue
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The kinds of the prologue's events. -/
def ProKind : Kind → Prop
  | .shfl .. | .elect .. | .mbInit .. | .fenceMbarInit | .cluster _ => True
  | _ => False

def isInit : Kind → Bool
  | .mbInit .. => true
  | _ => false

def isFence : Kind → Bool
  | .fenceMbarInit => true
  | _ => false

def isCluster : Kind → Bool
  | .cluster _ => true
  | _ => false

def isElect : Kind → Bool
  | .elect .. => true
  | _ => false

/-- The elections before a site of a thread of warp `w ≠ 0`: warp 12's one election, before its
initialization of the handshake barrier. -/
def Site.elects (w : Nat) : Site → Nat
  | .shfl0 | .shfl1 | .shfl2 | .elect12 => 0
  | .init320 => 1
  | _ => if w = 12 then 1 else 0

/-- Warp 0's elections before a site: one per election group passed (its fourteen elections, the
rank broadcast after the second). -/
def Site.elects0 : Site → Nat
  | .elect k => k.val
  | .init j => (groupOf j).val + 1
  | .shfl3 => 2
  | .fence1 | .clArrive | .clWait => 14
  | _ => 0

theorem elects0_group : ∀ k : Fin 14, (Site.init (groupStart k)).elects0 = k.val + 1 ∧
    (afterGroup k).elects0 = k.val + 1 := by decide

theorem elects0_init : ∀ j : Fin 36, (initNext j).elects0 = (Site.init j).elects0 := by decide

/-- Warp 0's initializations before the site have indices below this bound. -/
def Site.bound : Site → Nat
  | .elect e => (groupStart e).val
  | .init j => j.val
  | .shfl3 => 4
  | .fence1 | .clArrive | .clWait => 36
  | _ => 0

/-- The fences of the initializations before the site. -/
def Site.fences : Site → Nat
  | .shfl0 | .shfl1 | .shfl2 | .elect12 | .init320 | .fence0 => 0
  | .clArrive | .clWait => 2
  | _ => 1

/-- The site is after warp 12's initialization of the handshake barrier. -/
def Site.late : Site → Bool
  | .shfl0 | .shfl1 | .shfl2 | .elect12 | .init320 => false
  | _ => true

/-- The cluster-barrier operations before the site. -/
def Site.clusters : Site → Nat
  | .clWait => 1
  | _ => 0

/-- The site is an initialization, reached after an election that returned the thread's lane. -/
def Site.led : Site → Bool
  | .init _ | .init320 => true
  | _ => false

/-- The barriers of the thread's warp that the site has passed are initialized in `es`: warp
0's of index below the site's bound, warp 12's handshake barrier after `init320`. -/
def Done (L : Launch) (g : Nat) (s : Site) (es : List Event) : Prop :=
  (warpOf L g = 0 → ∀ j : Fin 36, j.val < s.bound →
    ∃ e ∈ es, e.kind = .mbInit (FBar.loc L (ctaOf L g) (FBar.ofInit j)) (FBar.ofInit j).count) ∧
  (warpOf L g = 12 → s.late = true →
    ∃ e ∈ es, e.kind = .mbInit (FBar.loc L (ctaOf L g) .dealloc) FBar.dealloc.count)

/-- The barrier an initialization event names, with its count. -/
def InitOk (L : Launch) (g : Nat) (s : Site) (k : Kind) : Prop :=
  ∀ m c, k = .mbInit m c →
    (∃ j : Fin 36, j.val < s.bound ∧ warpOf L g = 0 ∧
      m = FBar.loc L (ctaOf L g) (FBar.ofInit j) ∧ c = (FBar.ofInit j).count) ∨
    (s.late = true ∧ warpOf L g = 12 ∧ m = FBar.loc L (ctaOf L g) .dealloc ∧
      c = FBar.dealloc.count)

/-- **The prologue's run invariant.** -/
structure Run (L : Launch) (g : Nat) (p : D) (es : List Event) : Prop where
  kinds : ∀ e ∈ es, ProKind e.kind
  inits : ∀ e ∈ es, InitOk L g p.site e.kind
  nodup : ((es.filter (isInit ·.kind)).map Event.kind).Nodup
  fenced : ∀ i (h : i < es.length), isInit es[i].kind = true →
    (es.take i).countP (isFence ·.kind) < 2
  fences : es.countP (isFence ·.kind) = p.site.fences
  clusters : es.countP (isCluster ·.kind) = p.site.clusters
  mask : ElectMask 4294967295 es
  led : p.site.led = true → Elected es (laneOf L g)
  done : ElectLead L g es → Done L g p.site es
  /-- A thread of a warp other than 0 makes the warp's fixed elections. -/
  elects : warpOf L g ≠ 0 → es.countP (isElect ·.kind) = p.site.elects (warpOf L g)
  /-- A thread of warp 0 makes one election per election group. -/
  elects0 : warpOf L g = 0 → es.countP (isElect ·.kind) = p.site.elects0

/-- The event a prologue site fires, when the machine continues. -/
def EvOk (L : Launch) (g : Nat) : Site → Kind → Prop
  | .shfl0, k | .shfl1, k | .shfl2, k | .shfl3, k => ∃ md a b c r ok, k = .shfl md a b c r ok
  | .elect12, k | .elect _, k => ∃ i l, k = .elect 4294967295 i l
  | .init j, k => k = .mbInit (FBar.loc L (ctaOf L g) (FBar.ofInit j)) (FBar.ofInit j).count
  | .init320, k => k = .mbInit (FBar.loc L (ctaOf L g) .dealloc) FBar.dealloc.count
  | .fence0, k | .fence1, k => k = .fenceMbarInit
  | .clArrive, k | .clWait, k => ∃ op, k = .cluster op

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {p : D} {t : TState} {e : Event}
  {ins : Instr} {o : Option TState}

/-- The election instructions' full member mask. -/
theorem readBits_full {L : Launch} {g : Nat} {t : TState} :
    readBits L g t 32 (.imm (-1)) = .ok (BitVec.ofNat 64 4294967295) := rfl

set_option maxHeartbeats 4000000 in
/-- The event of a prologue site: of the site's kind, or undefined behaviour at a shuffle or an
election, after which the machine does not continue. -/
theorem event_cases {A : List Assumption} (hpre : Pre P L mem0)
    (h : At t p.site.pc (facts L g p)) (hc : kernel.code[p.site.pc]? = some ins)
    (hf : Fires p.site.pc (eventTmpl A L g t ins.op) e o) :
    EvOk L g p.site e.kind ∨ ((∃ f, e.kind = .ub f) ∧ ∀ x, next L g p e ≠ some (some x)) := by
  obtain ⟨s⟩ := p
  have hop := eventTmpl_opTmpl (A := A) (L := L) (g := g) (t := t) ins.op
  cases s with
  | init j => left; rw [init_event hpre j h hc hf]; rfl
  | init320 => left; rw [init320_event hpre h hc hf]; rfl
  | fence0 =>
    left
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceMbarInit_0)
    simp only [eventTmpl, tmaTmpl, widenMbarScope] at hf
    split at hf <;> (rw [hf.1]; rfl)
  | fence1 =>
    left
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceMbarInit_1)
    simp only [eventTmpl, tmaTmpl, widenMbarScope] at hf
    split at hf <;> (rw [hf.1]; rfl)
  | clArrive =>
    left
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterArrive_0)
    exact ⟨_, by rw [hf.1]⟩
  | clWait =>
    left
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterWait_0)
    exact ⟨_, by rw [hf.1]⟩
  | _ =>
    first
      | (obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_0))
      | (obtain ⟨dst, hc', -, -⟩ := code_elect ‹Fin 14›; rw [hc] at hc'; cases hc')
      | (obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_0))
      | (obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_1))
      | (obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_2))
      | (obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_3))
    all_goals first
      | (rcases fires_elect_mask readBits_full hf with ⟨i, l, rfl⟩ | ⟨f, rfl⟩
         · exact .inl ⟨i, l, rfl⟩
         · exact .inr ⟨⟨f, rfl⟩, fun x hx => by simp [next] at hx⟩)
      | (rcases hop with ⟨f, hm⟩ | ⟨md, a, b, c, k, hm⟩ <;> rw [hm] at hf
         · obtain ⟨rfl, -⟩ := hf
           exact .inr ⟨⟨f, rfl⟩, fun x hx => by simp [next] at hx⟩
         · obtain ⟨r, ok, rfl, -⟩ := hf
           exact .inl ⟨_, _, _, _, _, _, rfl⟩)

/-- The event of a prologue site after which the machine continues. -/
theorem event_ok {A : List Assumption} {x : D ⊕ RoleKind} (hpre : Pre P L mem0)
    (h : At t p.site.pc (facts L g p)) (hc : kernel.code[p.site.pc]? = some ins)
    (hf : Fires p.site.pc (eventTmpl A L g t ins.op) e o)
    (hn : next L g p e = some (some x)) : EvOk L g p.site e.kind :=
  (event_cases hpre h hc hf).resolve_right fun hu => hu.2 x hn

/-- How a prologue transition moves the run's counters. -/
structure Moves (s s' : Site) : Prop where
  bound : s.bound ≤ s'.bound
  init : ∀ j, s = .init j → j.val < s'.bound
  late : s.late = true → s'.late = true
  late320 : s = .init320 → s'.late = true
  fences : s'.fences = s.fences + (if s = .fence0 ∨ s = .fence1 then 1 else 0)
  clusters : s'.clusters = s.clusters + (if s = .clArrive then 1 else 0)

theorem moves_afterGroup : ∀ k : Fin 14, Moves (.elect k) (afterGroup k) := by
  intro k
  constructor <;> revert k <;> decide

theorem moves_elect : ∀ k : Fin 14, Moves (.elect k) (.init (groupStart k)) := by
  intro k
  constructor <;> revert k <;> decide

theorem moves_init : ∀ j : Fin 36, Moves (.init j) (initNext j) := by
  intro j
  constructor <;> revert j <;> decide

theorem moves {x : D ⊕ RoleKind} {p' : D} (hn : next L g p e = some (some x))
    (hx : x = .inl p') : Moves p.site p'.site := by
  subst hx
  obtain ⟨s⟩ := p
  obtain ⟨s'⟩ := p'
  cases s <;> simp only [next] at hn
  all_goals (repeat' split at hn) <;> simp_all
  all_goals subst_vars
  all_goals first
    | exact moves_init _ | exact moves_elect _ | exact moves_afterGroup _
    | (constructor <;> decide)

theorem InitOk.mono {s s' : Site} {k : Kind} (h : InitOk L g s k) (hm : Moves s s') :
    InitOk L g s' k := by
  intro m c hk
  rcases h m c hk with ⟨j, hj, h1, h2, h3⟩ | ⟨hl, h1, h2, h3⟩
  · exact .inl ⟨j, lt_of_lt_of_le hj hm.bound, h1, h2, h3⟩
  · exact .inr ⟨hm.late hl, h1, h2, h3⟩

theorem EvOk.proKind {s : Site} {k : Kind} (h : EvOk L g s k) : ProKind k := by
  cases s <;> simp only [EvOk] at h <;> obtain ⟨_, _, _, _, _, _, rfl⟩ := h <;> trivial

theorem EvOk.fence {s : Site} {k : Kind} (h : EvOk L g s k) :
    isFence k = decide (s = .fence0 ∨ s = .fence1) := by
  cases s <;> simp only [EvOk] at h <;> obtain ⟨_, _, _, _, _, _, rfl⟩ := h <;> rfl

theorem EvOk.cluster {s : Site} {k : Kind} (h : EvOk L g s k) (hs : s ≠ .clWait) :
    isCluster k = decide (s = .clArrive) := by
  cases s <;> simp only [EvOk] at h <;> obtain ⟨_, _, _, _, _, _, rfl⟩ := h <;>
    first | rfl | exact absurd rfl hs

/-- The initializing sites and their events. -/
theorem EvOk.init {s : Site} {k : Kind} (h : EvOk L g s k) (hk : isInit k = true) :
    (∃ j, s = .init j ∧
      k = .mbInit (FBar.loc L (ctaOf L g) (FBar.ofInit j)) (FBar.ofInit j).count) ∨
    (s = .init320 ∧ k = .mbInit (FBar.loc L (ctaOf L g) .dealloc) FBar.dealloc.count) := by
  cases s <;> simp only [EvOk] at h <;> obtain ⟨_, _, _, _, _, _, rfl⟩ := h <;>
    simp_all [isInit]

/-- Every election of the prologue has the full member mask. -/
theorem EvOk.mask {s : Site} {k : Kind} (h : EvOk L g s k) :
    ∀ mask inst ld, k = .elect mask inst ld → mask = 4294967295 := by
  intro mask inst ld hk
  subst hk
  cases s <;> simp_all [EvOk]

/-- The cluster-barrier operations are the arrival's and the wait's. -/
theorem EvOk.cluster_site {s : Site} {op : ClusterOp} (h : EvOk L g s (.cluster op)) :
    s = .clArrive ∨ s = .clWait := by
  cases s <;> simp_all [EvOk]

theorem Done.snoc {s : Site} {es : List Event} (h : Done L g s es) (e : Event) :
    Done L g s (es ++ [e]) :=
  ⟨fun hw j hj => by
    obtain ⟨x, hx, hk⟩ := h.1 hw j hj
    exact ⟨x, List.mem_append_left _ hx, hk⟩,
   fun hw hl => by
    obtain ⟨x, hx, hk⟩ := h.2 hw hl
    exact ⟨x, List.mem_append_left _ hx, hk⟩⟩

/-- `Done` at a site whose bound (for warp 0) and lateness (for warp 12) do not grow. -/
theorem Done.mono {s s' : Site} {es : List Event} (h : Done L g s es)
    (hb : warpOf L g = 0 → s'.bound ≤ s.bound)
    (hl : warpOf L g = 12 → s'.late = true → s.late = true) : Done L g s' es :=
  ⟨fun hw j hj => h.1 hw j (lt_of_lt_of_le hj (hb hw)), fun hw h' => h.2 hw (hl hw h')⟩

theorem bound_initNext : ∀ j : Fin 36, (initNext j).bound = j.val + 1 := by decide

theorem led_afterGroup : ∀ k : Fin 14, (afterGroup k).led = false := by decide

/-- A site reached after an election that returned the thread's lane: its predecessor was one,
or the event is that election. -/
theorem led_step {p' : D} (hn : next L g p e = some (some (.inl p'))) (hl : p'.site.led = true) :
    p.site.led = true ∨ ∃ mask inst, e.kind = .elect mask inst (laneOf L g) := by
  obtain ⟨s⟩ := p
  obtain ⟨s'⟩ := p'
  change s'.led = true at hl
  change s.led = true ∨ _
  cases s <;> simp only [next] at hn
  all_goals (repeat' split at hn) <;>
    simp only [Option.some.injEq, reduceCtorEq, Sum.inl.injEq, D.mk.injEq] at hn
  all_goals subst hn
  all_goals first
    | (left; rfl)
    | (rename_i hk hlane; right; exact ⟨_, _, by rw [hlane]; exact hk⟩)
    | (rw [led_afterGroup] at hl; cases hl)
    | (simp [Site.led] at hl)

/-- `Done` is kept along a step taken while every election returned the thread's lane. -/
theorem done_step {p' : D} {pre : List Event} (hJ : Done L g p.site pre)
    (hev : EvOk L g p.site e.kind) (hn : next L g p e = some (some (.inl p')))
    (hl : ElectLead L g (pre ++ [e])) : Done L g p'.site (pre ++ [e]) := by
  have hd := hJ.snoc e
  have he : e ∈ pre ++ [e] := List.mem_append_right _ (List.mem_singleton_self e)
  obtain ⟨s⟩ := p
  obtain ⟨s'⟩ := p'
  change Done L g s (pre ++ [e]) at hd
  change EvOk L g s e.kind at hev
  change Done L g s' (pre ++ [e])
  cases s <;> simp only [next] at hn
  all_goals (repeat' split at hn) <;>
    simp only [Option.some.injEq, reduceCtorEq, Sum.inl.injEq, D.mk.injEq] at hn
  all_goals subst hn
  all_goals first
    | exact hd.mono (fun _ => by decide) (fun _ => by decide)
    | exact hd.mono (fun _ => le_refl _) (fun _ h => h)
    | exact hd.mono (fun hw => absurd hw ‹_›) (fun _ => by decide)
    | exact hd.mono (fun _ => by decide) (fun hw => absurd hw ‹_›)
    | (rename_i hk hlane; exact absurd ((electLead_snoc_elect hk).mp hl).2.symm hlane)
    | exact ⟨fun _ j hj => absurd hj (by simp [Site.bound]), fun _ _ => ⟨e, he, hev⟩⟩
    | (rename_i j
       refine ⟨fun hw j' hj' => ?_, fun hw _ => hd.2 hw rfl⟩
       rw [bound_initNext] at hj'
       rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | hj'
       · exact hd.1 hw j' hj'
       · obtain rfl := Fin.ext hj'
         exact ⟨e, he, hev⟩)

/-- The elections of a step of warp 0. -/
theorem elects0_step {p' : D} (hw : warpOf L g = 0) (hi : Inv L g p) (hev : EvOk L g p.site e.kind)
    (hn : next L g p e = some (some (.inl p'))) :
    p'.site.elects0 = p.site.elects0 + (if isElect e.kind then 1 else 0) := by
  obtain ⟨s⟩ := p
  obtain ⟨s'⟩ := p'
  simp only at hev hn ⊢
  cases s <;> simp only [next] at hn
  case elect12 => exact absurd (hi.warp12 (.inl rfl)) (by omega)
  case init320 => exact absurd (hi.warp12 (.inr rfl)) (by omega)
  case elect k =>
    simp only [EvOk] at hev
    obtain ⟨_, _, hev⟩ := hev
    rw [hev] at hn
    simp only [Option.some.injEq, Sum.inl.injEq, D.mk.injEq] at hn
    subst hn
    have hE : isElect e.kind = true := by rw [hev]; rfl
    simp only [hE, ↓reduceIte]
    split
    · exact (elects0_group k).1.trans (by simp [Site.elects0])
    · exact (elects0_group k).2.trans (by simp [Site.elects0])
  case init j =>
    simp only [Option.some.injEq, Sum.inl.injEq, D.mk.injEq] at hn
    subst hn
    simp only [EvOk] at hev
    rw [elects0_init]
    simp [isElect, hev]
  all_goals simp only [EvOk] at hev
  all_goals (repeat' split at hn) <;> simp only [Option.some.injEq, Sum.inl.injEq, D.mk.injEq,
    reduceCtorEq] at hn
  all_goals (try subst hn)
  all_goals (try obtain ⟨_, _, _, _, _, _, hev⟩ := hev)
  all_goals (try obtain ⟨_, hev⟩ := hev)
  all_goals simp_all [isElect, Site.elects0]

/-- The elections of a step of a warp other than 0. -/
theorem elects_step {p' : D} (hw : warpOf L g ≠ 0) (hi : Inv L g p) (hev : EvOk L g p.site e.kind)
    (hn : next L g p e = some (some (.inl p'))) :
    p'.site.elects (warpOf L g) =
      p.site.elects (warpOf L g) + (if isElect e.kind then 1 else 0) := by
  obtain ⟨s⟩ := p
  obtain ⟨s'⟩ := p'
  simp only at hev hn ⊢
  cases s <;> simp only [next] at hn
  case elect k => exact absurd (hi.warp0 (.inl ⟨k, rfl⟩)) hw
  case init j => exact absurd (hi.warp0 (.inr ⟨j, rfl⟩)) hw
  all_goals have h12 := hi.warp12
  all_goals simp only [EvOk] at hev h12
  all_goals (repeat' split at hn) <;> simp only [Option.some.injEq, Sum.inl.injEq, D.mk.injEq,
    reduceCtorEq, true_or, or_true, forall_const] at hn h12
  all_goals (try subst hn)
  all_goals (try obtain ⟨_, _, _, _, _, _, hev⟩ := hev)
  all_goals (try obtain ⟨_, _, hev⟩ := hev)
  all_goals (try obtain ⟨_, hev⟩ := hev)
  all_goals simp_all [isElect, Site.elects]

theorem Run.step {p p' : D} {pre : List Event} (hJ : Run L g p pre) (hi : Inv L g p)
    (hev : EvOk L g p.site e.kind) (hm : Moves p.site p'.site) (hs : p.site ≠ .clWait)
    (hn : next L g p e = some (some (.inl p'))) :
    Run L g p' (pre ++ [e]) := by
  have hmask : ElectMask 4294967295 (pre ++ [e]) := fun x hx mask inst ld hk => by
    rcases List.mem_append.mp hx with hx | hx
    · exact hJ.mask x hx mask inst ld hk
    · rw [List.mem_singleton.mp hx] at hk
      exact hev.mask mask inst ld hk
  have hled : p'.site.led = true → Elected (pre ++ [e]) (laneOf L g) := fun hl => by
    rcases led_step hn hl with hl' | ⟨mask, inst, hk⟩
    · obtain ⟨x, hx, mask, inst, hk⟩ := hJ.led hl'
      exact ⟨x, List.mem_append_left _ hx, mask, inst, hk⟩
    · exact ⟨e, List.mem_append_right _ (List.mem_singleton_self e), mask, inst, hk⟩
  have hdone : ElectLead L g (pre ++ [e]) → Done L g p'.site (pre ++ [e]) := fun hl =>
    done_step (hJ.done hl.of_snoc) hev hn hl
  obtain ⟨s⟩ := p
  simp only at hev hm hs
  have hnew : InitOk L g p'.site e.kind := by
    intro m c hk
    rcases hev.init (by rw [hk]; rfl) with ⟨j, rfl, he⟩ | ⟨rfl, he⟩ <;> rw [hk] at he <;> cases he
    · exact .inl ⟨j, hm.init j rfl, hi.warp0 (.inr ⟨j, rfl⟩), rfl, rfl⟩
    · exact .inr ⟨hm.late320 rfl, hi.warp12 (.inr rfl), rfl, rfl⟩
  have hcolls : warpOf L g ≠ 0 → (pre ++ [e]).countP (isElect ·.kind) =
      p'.site.elects (warpOf L g) := fun hw => by
    rw [List.countP_append, hJ.elects hw, elects_step hw hi hev hn]
    simp
  have hcolls0 : warpOf L g = 0 → (pre ++ [e]).countP (isElect ·.kind) =
      p'.site.elects0 := fun hw => by
    rw [List.countP_append, hJ.elects0 hw, elects0_step hw hi hev hn]
    simp
  refine ⟨fun x hx => ?_, fun x hx => ?_, ?_, ?_, ?_, ?_, hmask, hled, hdone, hcolls, hcolls0⟩
  · rcases List.mem_append.mp hx with hx | hx
    · exact hJ.kinds x hx
    · rw [List.mem_singleton.mp hx]; exact hev.proKind
  · rcases List.mem_append.mp hx with hx | hx
    · exact (hJ.inits x hx).mono hm
    · rw [List.mem_singleton.mp hx]; exact hnew
  · rw [List.filter_append, List.map_append, List.nodup_append]
    refine ⟨hJ.nodup, ((List.filter_sublist (l := [e])).map _).nodup (by simp), ?_⟩
    intro a ha b hb hab
    subst hab
    simp only [List.mem_map, List.mem_filter, List.mem_singleton] at ha hb
    obtain ⟨x, ⟨hx, hxi⟩, rfl⟩ := ha
    obtain ⟨y, ⟨rfl, hyi⟩, hyx⟩ := hb
    have hold := hJ.inits x hx
    rcases hev.init hyi with ⟨j, rfl, he⟩ | ⟨rfl, he⟩
    · rw [hyx] at he
      rcases hold _ _ he with ⟨j', hj', -, h1, -⟩ | ⟨-, hw12, -⟩
      · have hoff := congrArg FBar.off (FBar.loc_inj h1).1
        rw [FBar.off_ofInit, FBar.off_ofInit] at hoff
        simp only [Site.bound] at hj'
        omega
      · have := hi.warp0 (.inr ⟨_, rfl⟩)
        omega
    · rw [hyx] at he
      rcases hold _ _ he with ⟨j', hj', -⟩ | ⟨hl, -⟩
      · simp [Site.bound] at hj'
      · simp [Site.late] at hl
  · intro i hi' hinit
    by_cases hlt : i < pre.length
    · rw [List.getElem_append_left hlt] at hinit
      rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
      exact hJ.fenced i hlt hinit
    · have hi'' : i = pre.length := by simp at hi'; omega
      subst hi''
      rw [List.getElem_append_right (Nat.le_refl _)] at hinit
      simp only [Nat.sub_self, List.getElem_singleton] at hinit
      rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length, hJ.fences]
      rcases hev.init hinit with ⟨j, rfl, -⟩ | ⟨rfl, -⟩ <;> simp [Site.fences]
  · rw [List.countP_append, hJ.fences, hm.fences]
    simp [hev.fence]
  · rw [List.countP_append, hJ.clusters, hm.clusters]
    simp [hev.cluster hs]

theorem run_nil : Run L g ⟨.shfl0⟩ [] :=
  ⟨by simp, by simp, by simp, by simp, rfl, rfl, fun _ h => absurd h List.not_mem_nil,
    fun h => absurd h (by decide), fun _ => ⟨fun _ _ h => absurd h (Nat.not_lt_zero _),
      fun _ h => absurd h (by decide)⟩, fun _ => rfl, fun _ => rfl⟩

/-- The prologue hands off at the cluster wait, to the role of the thread's warp. -/
theorem next_inr {k : RoleKind} (hn : next L g p e = some (some (.inr k))) :
    p.site = .clWait ∧ k = RoleKind.ofWarp (warpOf L g) := by
  obtain ⟨s⟩ := p
  cases s <;> simp only [next] at hn
  all_goals (repeat' split at hn) <;> simp_all

/-- The cluster wait leaves the prologue. -/
theorem next_clWait_inl {x : D ⊕ RoleKind} {p' : D} (hs : p.site = .clWait)
    (hn : next L g p e = some (some x)) : x ≠ .inl p' := by
  obtain ⟨s⟩ := p
  simp only at hs
  subst hs
  simp only [next, Option.some.injEq] at hn
  subst hn
  simp

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Prologue

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The prologue's invariant in the thread's prologue states. -/
def Prologue.RunJ (L : Launch) (g : Nat) : ThreadD → List Event → Prop
  | .inl p, es => Prologue.Run L g p es
  | .inr _, _ => True

/-- **The prologue's run invariant along a thread's run.** -/
theorem Prologue.run {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) {es : List Event}
    (htr : (code L g).toMachine.Trace (some (code L g).init) es) :
    ∀ j p, (code L g).toMachine.after (some (code L g).init) (es.take j) = some (some (.inl p)) →
      Prologue.Run L g p (es.take j) := by
  have h := Code.run_inv (sound hpre hg) htr (Prologue.RunJ L g) Prologue.run_nil ?_
  · exact fun j p hp => h j (.inl p) hp
  intro d d' pre e t ins o hJ hat hinv hc hf hn
  rcases d with p | r
  · change (Prologue.next L g p e).map (Option.bind · (handoff L g)) = some (some d') at hn
    cases hx : Prologue.next L g p e with
    | none => rw [hx] at hn; cases hn
    | some x =>
      rw [hx] at hn
      cases x with
      | none => cases hn
      | some x =>
        cases x with
        | inl p' =>
          simp only [Option.map_some, Option.bind_some, handoff, Option.some.injEq] at hn
          subst hn
          have hat' : At t p.site.pc (Prologue.facts L g p) :=
            ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩
          exact Prologue.Run.step hJ hinv (Prologue.event_ok hpre hat' hc hf hx)
            (Prologue.moves hx rfl) (fun hs => Prologue.next_clWait_inl hs hx rfl) hx
        | inr k =>
          simp only [Option.map_some, Option.bind_some, handoff] at hn
          cases hk : Role.start L g k with
          | none => rw [hk] at hn; cases hn
          | some r =>
            rw [hk] at hn
            simp only [Option.map_some, Option.some.injEq] at hn
            subst hn
            trivial
  · obtain ⟨r', rfl, -⟩ := code_next_inr hn
    trivial

/-- A role state's role is that of the thread's warp. -/
def RoleWarpJ (L : Launch) (g : Nat) : ThreadD → List Event → Prop
  | .inl _, _ => True
  | .inr r, _ => r.kind.Warp (warpOf L g)

/-- **Routing along a thread's run**: a thread in a role runs it on a warp of that role. -/
theorem role_warp_run {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) {es : List Event}
    (htr : (code L g).toMachine.Trace (some (code L g).init) es) :
    ∀ j r, (code L g).toMachine.after (some (code L g).init) (es.take j) = some (some (.inr r)) →
      r.kind.Warp (warpOf L g) := by
  have h := Code.run_inv (sound hpre hg) htr (RoleWarpJ L g) trivial ?_
  · exact fun j r hr => h j (.inr r) hr
  intro d d' pre e t ins o _ _ _ _ _ hn
  rcases d with p | r
  · change (Prologue.next L g p e).map (Option.bind · (handoff L g)) = some (some d') at hn
    cases hx : Prologue.next L g p e with
    | none => rw [hx] at hn; cases hn
    | some x =>
      rw [hx] at hn
      cases x with
      | none => cases hn
      | some x =>
        cases x with
        | inl p' =>
          simp only [Option.map_some, Option.bind_some, handoff, Option.some.injEq] at hn
          subst hn
          trivial
        | inr k =>
          simp only [Option.map_some, Option.bind_some, handoff] at hn
          have hk : k = RoleKind.ofWarp (warpOf L g) := by
            obtain ⟨s⟩ := p
            cases s <;> simp only [Prologue.next] at hx
            all_goals (repeat' split at hx) <;> simp_all
          cases hst : Role.start L g k with
          | none => rw [hst] at hn; cases hn
          | some r =>
            rw [hst] at hn
            simp only [Option.map_some, Option.some.injEq] at hn
            subst hn
            show r.kind.Warp (warpOf L g)
            rw [Role.start_kind hst, hk]
            exact RoleKind.warp_ofWarp (warpOf_lt hpre g)
  · obtain ⟨r', rfl, hk⟩ := code_next_inr hn
    show r'.kind.Warp (warpOf L g)
    rwa [hk]

end
end PTX.Kernels.FlashAttn4Fwd.Proof
