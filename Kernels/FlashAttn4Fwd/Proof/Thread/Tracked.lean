-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.TrackedCount
public import Lemmas.Flow.Shuffle
public import Lemmas.Step.WarpLanes

@[expose] public section

/-! # The machine follows every thread

The thread's machine gives up (`some none`) only at a shuffle that
does not return the value the state expects (`opv`: the shared base, the warp index, the
cluster rank, the CTA's rank, the Q descriptor, a descriptor word or a Tensor Memory column).
Every shuffle is a full-warp `shfl.sync.idx` from lane 0 whose operand is the state's expected
value (`shfl_form`), so a shuffle returns lane 0's operand (DEP-WARP-SHUFFLE) unless lane 0 exited
before it.

Lane 0's operand is the thread's own: the `n`-th shuffles of two lanes of a warp are at states
with the same shuffle count (`TrackedCount.lean`), which determines the site and the
coordinates the expected value depends on (`opv_eq`); and a lane at its exit has made more
shuffles than any lane of its warp makes (`exit_cnt`). By induction on the shuffle count, the
machine follows every thread (`tracked`). The softmax machine never gives up: it records the
words a Tensor Memory load returns, whatever they are, and stops only at a dead thread
(`Softmax.next_ne`). The barrier initializations' facts follow (`initFacts'`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The value a state's shuffle broadcasts from lane 0 (`b32 0` away from a shuffle). -/
def opv (L : Launch) (g : Nat) : ThreadD → Value
  | .inl p => match p.site with
    | .shfl0 => Prologue.sb L 0
    | .shfl1 | .shfl2 => b32 (warpOf L g)
    | .shfl3 => b32 (rankOf L g)
    | _ => b32 0
  | .inr (.loader _) => b32 (ctaOf L g % 2)
  | .inr (.mma d) => match d.site with
    | .shflQ => b32 (Mma.qLo L false)
    | .shfl k => Mma.shflVal L d k
    | _ => b32 0
  | .inr _ => b32 0

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- A full-warp broadcast from lane 0 of a register valued `v` by the facts. -/
theorem shfl_at {pc dst r : Nat} {ty : Option DType} {mask : Opnd} {live : List Nat}
    {val : Nat → Value} {v : Value} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hcode : kernel.code[pc]? = some ⟨none, .warp ⟨.shfl .idx, ty, [some dst],
      [.reg r, .imm 0, .imm 31], some mask⟩⟩)
    (hr : r ∈ live) (hv : val r = v) (hF : Holds t.regs (factsFrom live val))
    (hc : kernel.code[pc]? = some ins) (hf : Fires pc (eventTmpl asms L g t ins.op) e o)
    (hs : Execution.isShfl e = true) : ∃ recv ok, e = ⟨pc, .shfl .idx v 0 31 recv ok⟩ := by
  obtain rfl := Option.some.inj (hc.symm.trans hcode)
  exact fires_shfl_idx (p := none) (hv ▸ holds_mem hF (mem_factsFrom hr)) hf hs

/-- **A shuffle at a state broadcasts the state's value.** -/
theorem shfl_form {d : ThreadD} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hat : (code L g).AtD d t) (hc : kernel.code[(code L g).pc d]? = some ins)
    (hf : Fires ((code L g).pc d) (eventTmpl asms L g t ins.op) e o)
    (hs : Execution.isShfl e = true) :
    isShflSite d = true ∧
      ∃ recv ok, e = ⟨(code L g).pc d, .shfl .idx (opv L g d) 0 31 recv ok⟩ := by
  have hF := hat.2.2.2.2
  rcases d with p | r
  · obtain ⟨s⟩ := p
    cases hss : s.isShfl
    · exact absurd hs (by
        rw [not_shfl_of (d := .inl ⟨s⟩) (Prologue.site_shfl_pc _ hss) hc hf]; simp)
    refine ⟨hss, ?_⟩
    cases s <;> simp only [Prologue.Site.isShfl, reduceCtorEq] at hss
    · exact shfl_at Flow.code_shfl_0 (by table_decide)
        (by simp [opv, Prologue.valueOf, Prologue.values, PTX.Flow.lookupLit])
        hF hc hf hs
    · exact shfl_at Flow.code_shfl_1 (by table_decide)
        (by simp [opv, Prologue.valueOf, Prologue.values, PTX.Flow.lookupLit])
        hF hc hf hs
    · exact shfl_at Flow.code_shfl_2 (by table_decide)
        (by simp [opv, Prologue.valueOf, Prologue.values, PTX.Flow.lookupLit])
        hF hc hf hs
    · exact shfl_at Flow.code_shfl_3 (by table_decide)
        (by simp [opv, Prologue.valueOf, Prologue.values, PTX.Flow.lookupLit])
        hF hc hf hs
  · cases r with
    | loader l =>
      by_cases hh : l.site = .head
      · obtain ⟨s, i, tt, ks, ph, qp⟩ := l
        simp only at hh
        subst hh
        exact ⟨by simp [isShflSite], shfl_at Flow.code_shfl_4 (by table_decide)
          (by simp [opv, Loader.valueOf, Loader.table, Prologue.valueOf, Prologue.values,
            PTX.Flow.lookupLit]) hF hc hf hs⟩
      · exact absurd hs (by
          rw [not_shfl_of (d := .inr (.loader l)) (Loader.site_shfl_pc _ hh) hc hf]; simp)
    | mma m =>
      cases hss : m.site.isShfl
      · exact absurd hs (by
          rw [not_shfl_of (d := .inr (.mma m)) (Mma.site_shfl_pc _ hss) hc hf]; simp)
      obtain ⟨s, i, tt, base, pro⟩ := m
      cases s <;> simp only [Mma.Site.isShfl, reduceCtorEq] at hss
      · exact ⟨rfl, shfl_at Flow.code_shfl_5 (by table_decide)
          (by simp [opv, Mma.valueOf, Mma.values, PTX.Flow.lookupLit]) hF hc hf hs⟩
      · rename_i k
        fin_cases k
        · exact ⟨rfl, shfl_at Flow.code_shfl_6 (by table_decide)
            (by simp [opv, Mma.valueOf, Mma.values, Mma.qVals, Mma.asmVals, Mma.shflVal,
              PTX.Flow.lookupLit]) hF hc hf hs⟩
        · exact ⟨rfl, shfl_at Flow.code_shfl_7 (by table_decide)
            (by simp [opv, Mma.valueOf, Mma.values, Mma.qVals, Mma.asmVals, Mma.shflVal,
              PTX.Flow.lookupLit]) hF hc hf hs⟩
        · exact ⟨rfl, shfl_at Flow.code_shfl_8 (by table_decide)
            (by simp [opv, Mma.valueOf, Mma.values, Mma.qVals, Mma.asmVals, Mma.shflVal,
              PTX.Flow.lookupLit]) hF hc hf hs⟩
        · exact ⟨rfl, shfl_at Flow.code_shfl_9 (by table_decide)
            (by simp [opv, Mma.valueOf, Mma.values, Mma.qVals, Mma.asmVals, Mma.shflVal,
              PTX.Flow.lookupLit]) hF hc hf hs⟩
        · exact ⟨rfl, shfl_at Flow.code_shfl_10 (by table_decide)
            (by simp [opv, Mma.valueOf, Mma.values, Mma.qVals, Mma.asmVals, Mma.shflVal,
              PTX.Flow.lookupLit]) hF hc hf hs⟩
        · exact ⟨rfl, shfl_at Flow.code_shfl_11 (by table_decide)
            (by simp [opv, Mma.valueOf, Mma.values, Mma.qVals, Mma.asmVals, Mma.shflVal,
              PTX.Flow.lookupLit]) hF hc hf hs⟩
        · exact ⟨rfl, shfl_at Flow.code_shfl_12 (by table_decide)
            (by simp [opv, Mma.valueOf, Mma.values, Mma.qVals, Mma.asmVals, Mma.shflVal,
              PTX.Flow.lookupLit]) hF hc hf hs⟩
        · exact ⟨rfl, shfl_at Flow.code_shfl_13 (by table_decide)
            (by simp [opv, Mma.valueOf, Mma.values, Mma.qVals, Mma.asmVals, Mma.shflVal,
              PTX.Flow.lookupLit]) hF hc hf hs⟩
        · exact ⟨rfl, shfl_at Flow.code_shfl_14 (by table_decide)
            (by simp [opv, Mma.valueOf, Mma.values, Mma.qVals, Mma.asmVals, Mma.shflVal,
              PTX.Flow.lookupLit]) hF hc hf hs⟩
        · exact ⟨rfl, shfl_at Flow.code_shfl_15 (by table_decide)
            (by simp [opv, Mma.valueOf, Mma.values, Mma.qVals, Mma.asmVals, Mma.shflVal,
              PTX.Flow.lookupLit]) hF hc hf hs⟩
        · exact ⟨rfl, shfl_at Flow.code_shfl_16 (by table_decide)
            (by simp [opv, Mma.valueOf, Mma.values, Mma.qVals, Mma.asmVals, Mma.shflVal,
              PTX.Flow.lookupLit]) hF hc hf hs⟩
        · exact ⟨rfl, shfl_at Flow.code_shfl_17 (by table_decide)
            (by simp [opv, Mma.valueOf, Mma.values, Mma.qVals, Mma.asmVals, Mma.shflVal,
              PTX.Flow.lookupLit]) hF hc hf hs⟩
        · exact ⟨rfl, shfl_at Flow.code_shfl_18 (by table_decide)
            (by simp [opv, Mma.valueOf, Mma.values, Mma.qVals, Mma.asmVals, Mma.shflVal,
              PTX.Flow.lookupLit]) hF hc hf hs⟩
        · exact ⟨rfl, shfl_at Flow.code_shfl_19 (by table_decide)
            (by simp [opv, Mma.valueOf, Mma.values, Mma.qVals, Mma.asmVals, Mma.shflVal,
              PTX.Flow.lookupLit]) hF hc hf hs⟩
    | idle x => exact absurd hs (by
        rw [not_shfl_of (d := .inr (.idle x)) (Idle.site_not_shfl _) hc hf]; simp)
    | store x => exact absurd hs (by
        rw [not_shfl_of (d := .inr (.store x)) (Store.site_not_shfl _) hc hf]; simp)
    | softmax x => exact absurd hs (by
        rw [not_shfl_of (d := .inr (.softmax x)) (Softmax.site_not_shfl _) hc hf]; simp)
    | corr x => exact absurd hs (by
        rw [not_shfl_of (d := .inr (.corr x)) (Correction.site_not_shfl _) hc hf]; simp)


/-! ### The machine continues past a shuffle of the expected value -/

/-- A role's successor, mapped into the thread's states, is not `some none` when the role's own
successor is not. -/
theorem map_next_ne {α β : Type} {o : Option (Option α)} (F : α → β) (h : o ≠ some none) :
    o.map (Option.map F) ≠ some none := by
  rcases o with _ | _ | a
  · simp
  · exact absurd rfl h
  · simp

theorem Store.next_ne (L : Launch) (g : Nat) (d : Store.D) (e : Event) :
    Store.next L g d e ≠ some none := by
  intro h; unfold Store.next at h; repeat' split at h
  all_goals simp_all

theorem Correction.next_ne (L : Launch) (g : Nat) (d : Correction.D) (e : Event) :
    Correction.next L g d e ≠ some none := by
  intro h; unfold Correction.next at h; repeat' split at h
  all_goals simp_all

/-- The event a shuffle state expects: lane 0's broadcast of the state's value. -/
def ShflOk (L : Launch) (g : Nat) (d : ThreadD) (e : Event) : Prop :=
  Execution.isShfl e = true → ∃ pc, e = ⟨pc, .shfl .idx (opv L g d) 0 31 (opv L g d) true⟩

/-- **The machine continues** at a state of a thread whose role is composed, after an event
that is not a shuffle or is lane 0's broadcast of the expected value. -/
theorem next_ne {d : ThreadD} {e : Event} (hi : (code L g).inv d)
    (hcomp : (Role.start L g (RoleKind.ofWarp (warpOf L g))).isSome = true)
    (hok : ShflOk L g d e) :
    (code L g).next d e ≠ some none := by
  rcases d with p | r
  · change (Prologue.next L g p e).map (Option.bind · (handoff L g)) ≠ some none
    obtain ⟨s⟩ := p
    intro h
    cases hx : Prologue.next L g ⟨s⟩ e with
    | none => rw [hx] at h; cases h
    | some x =>
      rw [hx] at h
      cases x with
      | some x =>
        cases x with
        | inl p' => simp [handoff] at h
        | inr k =>
          have hk : k = RoleKind.ofWarp (warpOf L g) := by
            cases s <;> simp only [Prologue.next] at hx
            all_goals (repeat' split at hx) <;> simp_all
          subst hk
          simp only [Option.map_some, Option.bind_some, handoff] at h
          cases hst : Role.start L g (RoleKind.ofWarp (warpOf L g)) with
          | none => rw [hst] at hcomp; cases hcomp
          | some r => rw [hst] at h; cases h
      | none =>
        have hsh : Execution.isShfl e = true := by
          obtain ⟨pc, k⟩ := e
          cases s <;> simp only [Prologue.next] at hx <;> cases k <;>
            simp_all [Execution.isShfl]
        obtain ⟨pc, rfl⟩ := hok hsh
        cases s <;> simp [Prologue.next, opv, Prologue.sb, b32] at hx
  · cases r with
    | idle s =>
      apply map_next_ne
      intro h; obtain ⟨site⟩ := s; cases site <;> simp [Idle.next] at h
    | loader l =>
      apply map_next_ne
      intro h
      by_cases hs : Execution.isShfl e = true
      · obtain ⟨pc, rfl⟩ := hok hs
        obtain ⟨s, i, tt, ks, ph, qp⟩ := l
        cases s <;> simp [Loader.next, opv, b32, Work.rank] at h
      · obtain ⟨s, i, tt, ks, ph, qp⟩ := l
        obtain ⟨pc, k⟩ := e
        cases s <;> simp only [Loader.next] at h
        all_goals (repeat' split at h)
        all_goals simp_all [Execution.isShfl]
    | mma m =>
      apply map_next_ne
      intro h
      by_cases hs : Execution.isShfl e = true
      · obtain ⟨pc, rfl⟩ := hok hs
        obtain ⟨s, i, tt, base, pro⟩ := m
        cases s <;> simp only [Mma.next, opv] at h
        all_goals (repeat' split at h)
        all_goals simp_all
      · obtain ⟨s, i, tt, base, pro⟩ := m
        obtain ⟨pc, k⟩ := e
        cases s <;> simp only [Mma.next] at h
        all_goals (repeat' split at h)
        all_goals simp_all [Execution.isShfl]
    | store x => exact map_next_ne _ (Store.next_ne L g x e)
    | corr x => exact map_next_ne _ (Correction.next_ne L g x e)
    | softmax x => exact map_next_ne _ (Softmax.next_ne L g x e)


/-! ### Lanes at the same shuffle count -/

namespace Mma

theorem shfl_cnt (k : Fin 14) :
    shA (.shfl k) = (if k.val < 9 then 1 + k.val else k.val - 5) ∧
      (Site.shfl k).loop = (if k.val < 3 then 0 else 1) ∧
      region (.shfl k) = (if k.val < 3 then 1 else if k.val < 9 then 2 else 3) := by
  revert k; decide

theorem shflQ_cnt : shA .shflQ = 0 ∧ Site.shflQ.loop = 0 := by decide

theorem shflVal_congr {L : Launch} {d d' : D} (hi : d.i = d'.i) (ht : d.t = d'.t)
    (k : Fin 14) : shflVal L d k = shflVal L d' k := by
  fin_cases k <;> simp [shflVal, hi, ht]

/-- The shuffles before a broadcast `k` at trip `t` of item `i`, past the item's start. -/
theorem shfl_shfls {L : Launch} {g : Nat} {d : D} {k : Fin 14} (hs : d.site = .shfl k)
    (hi : Inv L g d) (hT : 1 ≤ trips L) :
    ∃ x, shfls L d = (6 * trips L + 2) * d.i + 1 + x ∧ x < 6 * trips L + 2 ∧
      x = (if k.val < 9 then k.val else k.val - 6) + 6 * d.t ∧
      (k.val < 3 → d.t = 0) ∧ (3 ≤ k.val → k.val < 9 → d.t + 1 < trips L) ∧
      (9 ≤ k.val → d.t + 1 = trips L) := by
  obtain ⟨hA, hl, hr⟩ := shfl_cnt k
  have htr := hi.trip
  unfold TripOk at htr
  rw [hs, hr] at htr
  simp only [shfls, cnt, hs, hA, hl]
  split_ifs at htr ⊢
  all_goals (try simp only at htr)
  all_goals exact ⟨_, by ring_nf; try omega, by omega, rfl, by omega, by omega, by omega⟩

/-- **Two broadcast states at the same count** are at the same broadcast, item and trip. -/
theorem shfl_decode {L : Launch} {g h : Nat} {d d' : D} (hT : 1 ≤ trips L)
    (hi : Inv L g d) (hi' : Inv L h d') (hp : d.site.phase = 0 → d.i = 0)
    (hp' : d'.site.phase = 0 → d'.i = 0) (hs : d.site.isShfl = true)
    (hs' : d'.site.isShfl = true) (hc : shfls L d = shfls L d') :
    (d.site = .shflQ ∧ d'.site = .shflQ) ∨
      (∃ k, d.site = .shfl k ∧ d'.site = .shfl k ∧ d.i = d'.i ∧ d.t = d'.t) := by
  have hq : ∀ {x : D}, x.site = .shflQ → (x.site.phase = 0 → x.i = 0) → shfls L x = 0 := by
    intro x hx hpx
    simp [shfls, cnt, hx, shflQ_cnt.1, shflQ_cnt.2, hpx (by rw [hx]; rfl)]
  obtain ⟨s, i, t, b, pr⟩ := d
  obtain ⟨s', i', t', b', pr'⟩ := d'
  simp only at hs hs' hp hp' hc ⊢
  cases s <;> simp only [Site.isShfl, reduceCtorEq] at hs <;>
    cases s' <;> simp only [Site.isShfl, reduceCtorEq] at hs'
  · exact .inl ⟨rfl, rfl⟩
  · rename_i k
    obtain ⟨x, hx, -⟩ := shfl_shfls (d := ⟨.shfl k, i', t', b', pr'⟩) rfl hi' hT
    rw [hq (x := ⟨.shflQ, i, t, b, pr⟩) rfl hp] at hc
    omega
  · rename_i k
    obtain ⟨x, hx, -⟩ := shfl_shfls (d := ⟨.shfl k, i, t, b, pr⟩) rfl hi hT
    rw [hq (x := ⟨.shflQ, i', t', b', pr'⟩) rfl hp'] at hc
    omega
  · rename_i k k'
    obtain ⟨x, hx, hxl, hxe, h1, h2, h3⟩ := shfl_shfls (d := ⟨.shfl k, i, t, b, pr⟩) rfl hi hT
    obtain ⟨x', hx', hxl', hxe', h1', h2', h3'⟩ :=
      shfl_shfls (d := ⟨.shfl k', i', t', b', pr'⟩) rfl hi' hT
    simp only at hx hx' hxe hxe' h1 h2 h3 h1' h2' h3'
    have hii : i = i' := by
      have e1 : ((6 * trips L + 2) * i + x) / (6 * trips L + 2) = i := by
        rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hxl, Nat.add_zero]
      have e2 : ((6 * trips L + 2) * i' + x') / (6 * trips L + 2) = i' := by
        rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hxl', Nat.add_zero]
      rw [← e1, ← e2]
      congr 1
      omega
    subst hii
    have hk : k = k' := by
      apply Fin.ext
      split_ifs at hxe hxe' <;> omega
    subst hk
    refine .inr ⟨k, rfl, rfl, rfl, ?_⟩
    split_ifs at hxe hxe' <;> omega

end Mma


theorem RoleKind.warp_unique {k k' : RoleKind} {w : Nat} (h : k.Warp w) (h' : k'.Warp w) :
    k = k' := by
  cases k <;> cases k' <;> simp only [RoleKind.Warp] at h h' <;> first | rfl | omega

theorem shflCnt_role (L : Launch) (g : Nat) (r : Role) : 4 ≤ shflCnt L g (.inr r) := by
  cases r <;> simp [shflCnt]

theorem trips_pos (hpre : Pre P L mem0) : 1 ≤ Mma.trips L := by
  have := skOf_eq hpre; have := hpre.skPos
  unfold Mma.trips; omega

/-- **Two lanes of a warp at the same shuffle count broadcast the same value.** -/
theorem opv_eq (hpre : Pre P L mem0) {g h : Nat} (hw : SameWarp L g h) {dg dh : ThreadD}
    {eg eh : List Event} (hJg : shflJ L g dg eg) (hJh : shflJ L h dh eh)
    (hig : (code L g).inv dg) (hih : (code L h).inv dh)
    (hkg : ∀ r, dg = .inr r → r.kind.Warp (warpOf L g))
    (hkh : ∀ r, dh = .inr r → r.kind.Warp (warpOf L h))
    (hsg : isShflSite dg = true) (hsh : isShflSite dh = true)
    (hc : shflCnt L g dg = shflCnt L h dh) : opv L g dg = opv L h dh := by
  have hwe : warpOf L g = warpOf L h := hw.2
  have hce : ctaOf L g = ctaOf L h := hw.1.2.2
  rcases dg with pg | rg <;> rcases dh with ph | rh
  · obtain ⟨sg⟩ := pg
    obtain ⟨sh⟩ := ph
    cases sg <;> simp only [isShflSite, Prologue.Site.isShfl, reduceCtorEq] at hsg <;>
      cases sh <;> simp only [isShflSite, Prologue.Site.isShfl, reduceCtorEq] at hsh <;>
      simp only [shflCnt, Prologue.Site.shfls] at hc <;>
      first | omega | simp [opv, hwe, rankOf, hce]
  · have := shflCnt_role L h rh
    obtain ⟨sg⟩ := pg
    have hc' : sg.shfls = shflCnt L h (.inr rh) := hc
    cases sg <;> simp only [isShflSite, Prologue.Site.isShfl, reduceCtorEq] at hsg <;>
      simp only [Prologue.Site.shfls] at hc' <;> omega
  · have := shflCnt_role L g rg
    obtain ⟨sh⟩ := ph
    have hc' : shflCnt L g (.inr rg) = sh.shfls := hc
    cases sh <;> simp only [isShflSite, Prologue.Site.isShfl, reduceCtorEq] at hsh <;>
      simp only [Prologue.Site.shfls] at hc' <;> omega
  · have hk := RoleKind.warp_unique (hkg rg rfl) (hwe ▸ hkh rh rfl)
    cases rg <;> cases rh <;> simp only [Role.kind, reduceCtorEq] at hk <;>
      simp only [isShflSite, Bool.false_eq_true] at hsg
    · simp [opv, hce]
    · rename_i m m'
      simp only [shflCnt, Nat.add_left_cancel_iff] at hc
      rcases Mma.shfl_decode (trips_pos hpre) hig.1 hih.1 hJg.1.pre hJh.1.pre hsg hsh hc with
        ⟨h1, h2⟩ | ⟨k, h1, h2, h3, h4⟩
      · simp [opv, h1, h2]
      · simp only [opv, h1, h2]
        exact Mma.shflVal_congr h3 h4 k


/-! ### A lane at its exit has made every shuffle of its warp -/

theorem Prologue.site_ne_exit (s : Prologue.Site) : s.pc ≠ Flow.exit_0 := by
  cases s <;> site_decide

theorem Loader.site_exit (s : Loader.Site) : s.pc = Flow.exit_0 → s = .exit := by
  cases s <;> site_decide

theorem Mma.site_exit (s : Mma.Site) : s.pc = Flow.exit_0 → s = .exit := by
  cases s <;> site_decide

theorem Mma.shfls_exit {L : Launch} {d : Mma.D} (hs : d.site = .exit) :
    Mma.shfls L d = (6 * Mma.trips L + 2) * d.i + 1 := by
  simp [Mma.shfls, Mma.cnt, hs, Mma.shA, Mma.Site.after, Mma.Site.inTrip, Mma.Site.ord,
    Mma.Site.loop, Mma.Site.phase]

/-- **A lane at its exit has made more shuffles** than any lane of its warp at a shuffle. -/
theorem exit_cnt (hpre : Pre P L mem0) {g h : Nat} (hw : SameWarp L g h) {dg dh : ThreadD}
    {eg eh : List Event} (hJg : shflJ L g dg eg) (hJh : shflJ L h dh eh)
    (hig : (code L g).inv dg) (hih : (code L h).inv dh)
    (hkg : ∀ r, dg = .inr r → r.kind.Warp (warpOf L g))
    (hkh : ∀ r, dh = .inr r → r.kind.Warp (warpOf L h))
    (hsg : isShflSite dg = true) (hx : (code L h).pc dh = Flow.exit_0) :
    shflCnt L g dg < shflCnt L h dh := by
  have hwe : warpOf L g = warpOf L h := hw.2
  have hce : ctaOf L g = ctaOf L h := hw.1.2.2
  rcases dh with ph | rh
  · exact absurd hx (Prologue.site_ne_exit ph.site)
  have h4 := shflCnt_role L h rh
  rcases dg with pg | rg
  · obtain ⟨sg⟩ := pg
    have hc' : shflCnt L g (.inl ⟨sg⟩) = sg.shfls := rfl
    rw [hc']
    cases sg <;> simp only [isShflSite, Prologue.Site.isShfl, reduceCtorEq] at hsg <;>
      simp only [Prologue.Site.shfls] <;> omega
  have hk := RoleKind.warp_unique (hkg rg rfl) (hwe ▸ hkh rh rfl)
  cases rg <;> cases rh <;> simp only [Role.kind, reduceCtorEq] at hk <;>
    simp only [isShflSite, Bool.false_eq_true, decide_eq_true_eq] at hsg
  · rename_i l l'
    have hs := Loader.site_exit l'.site hx
    have hT : l.i < Work.T L g := hig.item (by rw [hsg]; rfl)
    have hTe : Work.T L g = Work.T L h := by
      simp only [Work.T, Work.cid, clusterOf, ctaOf] at hT ⊢
      simp only [ctaOf] at hce
      rw [hce]
    simp only [shflCnt, Loader.shfls, hsg, hs]
    omega
  · rename_i m m'
    have hs := Mma.site_exit m'.site hx
    have hP : 0 < 6 * Mma.trips L + 2 := by omega
    simp only [shflCnt, Mma.shfls_exit hs]
    cases hq : m.site with
    | shflQ =>
      have := hJg.1.pre (by rw [hq]; rfl)
      simp [Mma.shfls, Mma.cnt, hq, Mma.shflQ_cnt.1, Mma.shflQ_cnt.2, this]
    | shfl k =>
      obtain ⟨x, hx1, hx2, -⟩ := Mma.shfl_shfls hq hig.1 (trips_pos hpre)
      obtain ⟨hwk, hr⟩ := hig.1.i (by rw [hq]; trivial)
      have hE := hJh.2.2 (by rw [hs]; rfl)
      have hre : Mma.rank L h = Mma.rank L g := by
        simp only [Mma.rank, ctaOf] at hr hce ⊢; rw [hce]
      have hwke : ∀ i, Mma.work L h i = Mma.work L g i := by
        intro i; simp only [Mma.work, clusterOf, ctaOf] at hce ⊢; rw [hce]
      have hlt := hE (hre ▸ hr)
      rw [hwke] at hlt
      have hii : m.i + 1 ≤ m'.i := by
        by_contra hc
        have : m'.i * Mma.clusters L ≤ m.i * Mma.clusters L :=
          Nat.mul_le_mul_right _ (by omega)
        simp only [Mma.work] at hwk hlt
        omega
      have := Nat.mul_le_mul_left (6 * Mma.trips L + 2) hii
      rw [hx1]
      rw [Nat.mul_add, Nat.mul_one] at this
      omega
    | _ => simp [hq, Mma.Site.isShfl] at hsg


/-! ### Every lane of a composed warp is followed -/

/-- The only `ret` of the kernel (the kernel has no `exit`). -/
def retOp : Op → Bool
  | .ret | .exit => true
  | _ => false

/-- An instruction that fires the exit event is a `ret` or an `exit`. -/
theorem retOp_of_fires {A : List Assumption} {L : Launch} {g : Nat} {t : TState} {op : Op}
    {pc : Nat} {e : Event} {o : Option TState} (hf : Fires pc (eventTmpl A L g t op) e o)
    (hk : e.kind = .exit) : retOp op = true := by
  rcases fires_exit_op hf hk with rfl | rfl <;> rfl

theorem kernel_ret_pcs : OpPcsFast kernel.code retOp [Flow.exit_0] = true := by
  decide +kernel

/-- Every warp's role is composed. -/
theorem comp_of (L : Launch) (g : Nat) :
    (Role.start L g (RoleKind.ofWarp (warpOf L g))).isSome = true := by
  generalize RoleKind.ofWarp (warpOf L g) = k
  cases k <;> rfl

variable {X : Execution}

/-- **The machine follows every lane of a warp of a composed role.** By induction on the
shuffle count: a lane's machine continues up to its `n`-th shuffle, which returns lane 0's
`n`-th operand, the lane's own expected value. -/
theorem tracked_shfl (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) {g : Nat} :
    ∀ n h, SameWarp L g h → ∀ j, ((X.tr h).take j).countP Execution.isShfl ≤ n →
      Frame.stateAt (code L) X h j ≠ some none := by
  have hC : ∀ g < L.threads, (code L g).Sound := fun _ hg => sound hpre hg
  have hpos : 0 < L.block := by rw [hpre.block]; decide
  -- the facts of a followed state before an event
  have facts : ∀ {h k : Nat} {d : ThreadD} {e : Event}, X.get (h, k) = some e →
      Frame.stateAt (code L) X h k = some (some d) →
      ∃ t ins o, (code L h).AtD d t ∧ (code L h).inv d ∧
        kernel.code[(code L h).pc d]? = some ins ∧
        Fires ((code L h).pc d) (eventTmpl asms L h t ins.op) e o ∧
        shflJ L h d ((X.tr h).take k) ∧ (∀ r, d = .inr r → r.kind.Warp (warpOf L h)) := by
    intro h k d e he hσ
    have hh := Frame.lt_of_get hX he
    have hk : k < (X.tr h).length := (List.getElem?_eq_some_iff.mp he).1
    obtain ⟨t, ins, o, hat, hi, hc, hf⟩ := Frame.fired_site hC hX he hσ
    refine ⟨t, ins, o, hat, hi, hc, hf, RunInv.holds hpre hX hh (shflJ_run hpre hh) hk hσ, ?_⟩
    rintro r rfl
    exact role_warp_run hpre hh (Frame.trace (C := code L) hC hX hh) k r hσ
  -- a non-ub event at a state that is not `some none` is at a followed state
  have live : ∀ {h k : Nat} {e : Event}, X.get (h, k) = some e → (∀ pc f, e ≠ ⟨pc, .ub f⟩) →
      Frame.stateAt (code L) X h k ≠ some none →
      ∃ d, Frame.stateAt (code L) X h k = some (some d) := by
    intro h k e he hub hne
    rcases Frame.fired hC hX he with ⟨σ, o, hσ, -⟩ | ⟨-, pc, f, rfl⟩
    · rcases σ with _ | d
      · exact absurd hσ hne
      · exact ⟨d, hσ⟩
    · exact absurd rfl (hub pc f)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro h hgh j
  induction j with
  | zero => intro _; rw [Frame.stateAt_zero]; simp
  | succ j ihj =>
    intro hcnt
    by_cases hj : j < (X.tr h).length
    · obtain ⟨e, he⟩ : ∃ e, (X.tr h)[j]? = some e := ⟨_, List.getElem?_eq_getElem hj⟩
      have htake : (X.tr h).take (j + 1) = (X.tr h).take j ++ [e] := by
        rw [List.take_add_one, he]; rfl
      rw [htake, List.countP_append] at hcnt
      have hprev := ihj (by omega)
      rw [Frame.stateAt_succ he]
      cases hσ : Frame.stateAt (code L) X h j with
      | none => intro h; cases h
      | some σ =>
        cases σ with
        | none => exact absurd hσ hprev
        | some d =>
        have he' : X.get (h, j) = some e := he
        obtain ⟨t, ins, o, hat, hi, hc, hf, hJ, hk⟩ := facts he' hσ
        simp only [Option.bind_some]
        refine next_ne hi (comp_of L h) ?_
        intro hs
        obtain ⟨hss, recv, ok, rfl⟩ := shfl_form hat hc hf hs
        -- the shuffle's index and lane 0's operand
        set n' := ((X.tr h).take j).countP Execution.isShfl with hn'
        have hlt : n' < n := by simp [Execution.isShfl] at hcnt; omega
        have hK : X.ShflK (h, j) n' := ⟨⟨_, _, _, _, _, _, _, he'⟩, rfl⟩
        obtain ⟨hok, hsrc⟩ := hX.shfl h j n' _ .idx _ 0 31 recv ok he' hK
        have hsrc0 : shflSource .idx (laneOf L h) 0 31 = (0, true) := by simp [shflSource]
        rw [hsrc0] at hok hsrc
        simp only [Nat.add_zero] at hok hsrc
        obtain ⟨hw0, -⟩ := laneZero_sameWarp hpos (Frame.lt_of_get hX he')
        have hg0 : SameWarp L g (h - laneOf L h) := Step.sameWarp_trans hgh hw0
        have hcnt0 : shflCnt L h d = n' := by rw [hn', hJ.2.1]
        suffices hr : recv = opv L h d by rw [hr, hok]; exact ⟨_, rfl⟩
        rcases hsrc with ⟨j0, pc0, b0, c0, r0, o0, hK0, he0⟩ | ⟨k0, pc0, hex, hcx⟩
        · -- lane 0's `n'`-th shuffle broadcasts its expected value, the lane's own
          have hc0 : ((X.tr (h - laneOf L h)).take j0).countP Execution.isShfl = n' := hK0.2
          obtain ⟨d0, hσ0⟩ := live he0 nofun (ihn n' hlt _ hg0 j0 hc0.le)
          obtain ⟨t0, ins0, o0', hat0, hi0, hc0', hf0, hJ0, hk0⟩ := facts he0 hσ0
          obtain ⟨hss0, recv0, ok0, he0'⟩ := shfl_form hat0 hc0' hf0 (by simp [Execution.isShfl])
          simp only [Event.mk.injEq, Kind.shfl.injEq] at he0'
          obtain ⟨-, -, hrecv, -⟩ := he0'
          have heq := opv_eq hpre hw0 hJ hJ0 hi hi0 hk hk0 hss hss0
            (by rw [hcnt0, hJ0.2.1.symm.trans hc0])
          rw [heq, hrecv]
        · -- lane 0 did not exit before its `n'`-th shuffle
          exfalso
          obtain ⟨d0, hσ0⟩ := live hex nofun (ihn n' hlt _ hg0 k0 hcx)
          obtain ⟨t0, ins0, o0', hat0, hi0, hc0', hf0, hJ0, hk0⟩ := facts hex hσ0
          have hret : retOp ins0.op = true := by
            exact retOp_of_fires hf0 rfl
          have hpc := OpPcsFast.mem kernel_ret_pcs hc0' hret
          simp only [List.mem_singleton] at hpc
          have := exit_cnt hpre hw0 hJ hJ0 hi hi0 hk hk0 hss hpc
          rw [hcnt0, ← hJ0.2.1] at this
          omega
    · have h1 : (X.tr h).take (j + 1) = (X.tr h).take j := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      rw [h1] at hcnt
      rw [Frame.stateAt_of_le (by omega)]
      rw [← Frame.stateAt_of_le (C := code L) (X := X) (g := h) (k := j) (by omega)]
      exact ihj hcnt


/-- **The machine follows every thread** at each of its events. -/
theorem tracked (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) :
    Frame.Tracked (code L) X :=
  fun g k hg => tracked_shfl hpre hX _ g ⟨⟨hg, hg, rfl⟩, rfl⟩ k le_rfl

/-- The barrier initializations' facts. -/
theorem initFacts' (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X) :
    InitFacts L X :=
  initFacts hpre hX (tracked hpre hX) (Role.noInitSite L)

end
end PTX.Kernels.FlashAttn4Fwd.Proof
