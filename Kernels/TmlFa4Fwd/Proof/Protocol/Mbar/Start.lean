-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Start0
public import Kernels.TmlFa4Fwd.Proof.Lib.Obj
public import Lemmas.Flow.Step.ShapeRegs
import Kernels.TmlFa4Fwd.Flow.Code.Part000
import Kernels.TmlFa4Fwd.Flow.Code.Part001
import Kernels.TmlFa4Fwd.Flow.Code.Part002
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Lemmas.Kernel.FrameU
import Kernels.TmlFa4Fwd.Proof.Lib.MbarInit
import Lemmas.Kernel.UbLast
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The startup's mbarrier objects and the CTA barrier

The facts about the startup that ERR-MBAR-UNINITIALIZED needs (`Protocol/Mbar/Init.lean`):

* **The objects** (`obj`, `initOff`): the startup of warp 0 initializes 34 mbarriers of its CTA,
  at the shared base plus `initOff n` (`init_ev`: the address register of each `mbarrier.init` is
  the shared base or the base plus a constant, by the startup's value table).
* **The CTA barrier comes first** (`role_bar0`): a role state of a thread follows its CTA barrier,
  since the startup enters a role only from its barrier site.
* **The elected lane's path** (`lead_path`): a lane of warp 0 whose every election returns its
  own lane index walks the fixed sequence `pathSite` of startup sites up to the barrier: the three
  shuffles, then each election followed by its block of initializations, the fence and the
  barrier. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### The objects -/

/-- The offset of the object each initialization initializes. -/
def initOff (n : Fin 34) : Nat :=
  [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104, 112, 120, 128, 136, 144, 152, 160, 168,
    176, 184, 192, 200, 208, 216, 224, 232, 320, 328, 336, 344].getD n.val 0

/-- The offsets of the startup's objects: the multiples of 8 below 240, and 320 to 344. -/
def ObjOff (o : Nat) : Prop := (o < 240 ∨ 320 ≤ o ∧ o < 352) ∧ o % 8 = 0

instance : DecidablePred ObjOff := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Every object offset is initialized by one of the startup's initializations. -/
theorem objOff_init {o : Nat} (h : ObjOff o) : ∃ n, initOff n = o := by
  obtain ⟨h1, h2⟩ := h
  have : o < 352 := by omega
  interval_cases o <;> simp_all <;> first
    | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩ | exact ⟨4, rfl⟩
    | exact ⟨5, rfl⟩ | exact ⟨6, rfl⟩ | exact ⟨7, rfl⟩ | exact ⟨8, rfl⟩ | exact ⟨9, rfl⟩
    | exact ⟨10, rfl⟩ | exact ⟨11, rfl⟩ | exact ⟨12, rfl⟩ | exact ⟨13, rfl⟩ | exact ⟨14, rfl⟩
    | exact ⟨15, rfl⟩ | exact ⟨16, rfl⟩ | exact ⟨17, rfl⟩ | exact ⟨18, rfl⟩ | exact ⟨19, rfl⟩
    | exact ⟨20, rfl⟩ | exact ⟨21, rfl⟩ | exact ⟨22, rfl⟩ | exact ⟨23, rfl⟩ | exact ⟨24, rfl⟩
    | exact ⟨25, rfl⟩ | exact ⟨26, rfl⟩ | exact ⟨27, rfl⟩ | exact ⟨28, rfl⟩ | exact ⟨29, rfl⟩
    | exact ⟨30, rfl⟩ | exact ⟨31, rfl⟩ | exact ⟨32, rfl⟩ | exact ⟨33, rfl⟩

/-- A 32-bit address word `x` below `2 ^ 32` plus an offset that stays below `2 ^ 32`. -/
theorem trunc_add {x : BitVec 64} {a n : Nat} (hx : x.toNat = a) (hlt : a + n < 2 ^ 32) :
    (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 (n : Int))).toNat = a + n := by
  have h1 : (truncBits 32 x).toNat = a := by
    simp only [truncBits, BitVec.toNat_ofNat, hx]; omega
  have h2 : (BitVec.ofInt 64 (n : Int)).toNat = n := by
    simp only [BitVec.toNat_ofInt]; omega
  simp only [truncBits, BitVec.toNat_ofNat, BitVec.toNat_add] at h1 ⊢
  rw [h1, h2]
  omega

/-- The object at a shared-base address word plus an offset. -/
theorem smLoc_of (hp : Pre p L m) {x : BitVec 64} {k : Nat} {off : Int} (h0 : 0 ≤ off)
    (hx : x.toNat = L.sharedBase + k) (hk : k + off.toNat < 1024) :
    smLoc L g x off = obj L g (k + off.toNat) := by
  have hs := hp.shared.2.1
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  simp only [Int.toNat_natCast] at hk ⊢
  simp only [smLoc, trunc_add hx (show L.sharedBase + k + n < 2 ^ 32 by omega), Nat.add_assoc]

theorem al_of (hp : Pre p L m) {x : BitVec 64} {k : Nat} {off : Int} (h0 : 0 ≤ off)
    (hx : x.toNat = L.sharedBase + k) (hk : k + off.toNat < 1024) (h8 : (k + off.toNat) % 8 = 0) :
    (truncBits 32 (truncBits 32 x + BitVec.ofInt 64 off)).toNat % 8 = 0 := by
  have hs := hp.shared.2.1
  have hsb := hp.shared.1
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  simp only [Int.toNat_natCast] at hk h8 ⊢
  rw [trunc_add hx (show L.sharedBase + k + n < 2 ^ 32 by omega)]
  omega

/-- The shared base word plus a constant, as a number. -/
theorem sb_toNat (hp : Pre p L m) {k : Nat} (hk : k < 1024) :
    (Arith32.addi (BitVec.ofNat 64 L.sharedBase) k).toNat = L.sharedBase + k := by
  have h : Arith32.addi (BitVec.ofNat 64 L.sharedBase) k = BitVec.ofNat 64 (L.sharedBase + k) :=
    Epilogue.sb_add hp hk
  rw [h, BitVec.toNat_ofNat]
  have := hp.shared.2.1
  omega

theorem sb_toNat0 (hp : Pre p L m) : (BitVec.ofNat 64 L.sharedBase).toNat = L.sharedBase + 0 := by
  have := hp.shared.2.1
  rw [BitVec.toNat_ofNat]; omega

set_option maxHeartbeats 8000000 in
/-- **The object each initialization initializes**: at a startup state of initialization `q`
with the shared base recorded, the event initializes `obj (initOff q)`, or is undefined
behaviour. -/
theorem init_ev (hp : Pre p L m) {s : Startup.D} {q : Fin 34} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (hs : s.site = .init q)
    (hx : s.x1 = BitVec.ofNat 64 L.sharedBase) (hat : (Startup.code p L g).AtD s t)
    (hc : kernel.code[s.site.pc]? = some ins)
    (hf : Fires s.site.pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    (∃ c, e.kind = .mbInit (obj L g (initOff q)) c) ∨ ∃ f, e.kind = .ub f := by
  have hreg : ∀ r ∈ Flow.live s.site.pc, t.regs r = some (Startup.valueOf p L g s r) :=
    fun r hr => holds_mem hat.2.2.2.2 (mem_factsFrom hr)
  have hsb := hp.shared.1
  obtain ⟨site, x1, x2, x3⟩ := s
  simp only at hs hx
  subst hs hx
  fin_cases q <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    rcases fires_mbInit_reg hf (hreg _ (by lit_mem)) (by
        first
          | exact al_of hp (by decide) (sb_toNat hp (by decide)) (by decide) (by decide)
          | exact al_of hp (by decide) (sb_toNat0 hp) (by decide) (by decide)) with
      ⟨c, hk⟩ | hu
    · refine .inl ⟨c, hk.trans ?_⟩
      congr 1
      first
        | exact smLoc_of hp (by decide) (sb_toNat hp (by decide)) (by decide)
        | exact smLoc_of hp (by decide) (sb_toNat0 hp) (by decide)
    · exact .inr hu

/-- The count of each of the startup's initializations, as the code's `mov.b32` before it sets
it. -/
def initCnt (q : Fin 34) : Nat :=
  [1, 1, 1, 1, 64, 64, 64, 1, 1, 1, 1, 1, 256, 256, 4, 4, 1, 1, 1, 1, 128, 128, 128, 128, 128, 128,
    128, 128, 32, 32, 1, 1, 4, 4].getD q.val 0

theorem readBits_bits {L : Launch} {g : Nat} {t : TState} {r : Nat} {x : BitVec 64}
    (h : t.regs r = some (.bits 32 x)) : readBits L g t 32 (.reg r) = .ok (truncBits 32 x) := by
  simp only [readBits, readReg, h, bind, Except.bind, pure, Except.pure]

set_option maxHeartbeats 8000000 in
/-- **The object and count of each initialization**: at a startup state of initialization `q`
with the shared base recorded, the event initializes `obj (initOff q)` with count `initCnt q`, or
is undefined behaviour. -/
theorem init_cnt (hp : Pre p L m) {s : Startup.D} {q : Fin 34} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (hs : s.site = .init q)
    (hx : s.x1 = BitVec.ofNat 64 L.sharedBase) (hat : (Startup.code p L g).AtD s t)
    (hc : kernel.code[s.site.pc]? = some ins)
    (hf : Fires s.site.pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    e.kind = .mbInit (obj L g (initOff q)) (initCnt q) ∨ ∃ f, e.kind = .ub f := by
  have hreg : ∀ r ∈ Flow.live s.site.pc, t.regs r = some (Startup.valueOf p L g s r) :=
    fun r hr => holds_mem hat.2.2.2.2 (mem_factsFrom hr)
  have hsb := hp.shared.1
  obtain ⟨site, x1, x2, x3⟩ := s
  simp only at hs hx
  subst hs hx
  fin_cases q <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    rcases fires_mbInit_cnt hf (hreg _ (by lit_mem)) (by
        first
          | exact al_of hp (by decide) (sb_toNat hp (by decide)) (by decide) (by decide)
          | exact al_of hp (by decide) (sb_toNat0 hp) (by decide) (by decide))
        (readBits_bits (hreg _ (by lit_mem))) with hk | hu
    · refine .inl (hk.trans ?_)
      congr 1
      first
        | exact smLoc_of hp (by decide) (sb_toNat hp (by decide)) (by decide)
        | exact smLoc_of hp (by decide) (sb_toNat0 hp) (by decide)
    · exact .inr hu

/-! ### The CTA barrier comes before every role state -/

theorem exit_of_mid {d : Startup.D} (h : d.site.mid = true) : exit L g d = none := by
  obtain ⟨site, _, _, _⟩ := d
  cases site <;> simp_all [exit, Startup.Site.mid]

/-- **The startup enters a role only from its barrier site.** -/
theorem succ_exit_bar {s s' : Startup.D} {e : Event} (h : Startup.succ L g s e = some (some s'))
    (hx : exit L g s' ≠ none) : s.site = .bar := by
  obtain ⟨site, x1, x2, x3⟩ := s
  refine (show site = .bar from ?_)
  cases site with
  | bar => rfl
  | enter r => simp [Startup.succ] at h
  | fence =>
    simp only [Startup.succ, Option.some.injEq] at h
    subst h
    exact absurd (exit_of_mid rfl) hx
  | elect j =>
    simp only [Startup.succ] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      split_ifs at hx
      · exact absurd (exit_of_mid (mid_firstInit j)) hx
      · exact absurd (exit_of_mid (mid_afterBlock _ j)) hx
    · simp at h
  | init q =>
    simp only [Startup.succ] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact absurd (exit_of_mid (mid_afterBlock _ _)) hx
    · simp only [Option.some.injEq] at h
      subst h
      exact absurd (exit_of_mid (mid_initSucc q)) hx
  | sh j =>
    simp only [Startup.succ] at h
    split at h
    · simp only [Startup.word32] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        fin_cases j
        · exact absurd (by simp [exit]) hx
        · exact absurd (by simp [exit]) hx
        · simp only at hx
          split_ifs at hx
          · exact absurd (exit_of_mid rfl) hx
          · exact absurd (exit_of_mid rfl) hx
      · simp at h
    · simp at h

theorem countP_take_mono' (P : Event → Bool) (es : List Event) {a b : Nat} (h : a ≤ b) :
    (es.take a).countP P ≤ (es.take b).countP P :=
  (List.take_sublist_take_left h).countP_le

/-- **A role state follows the thread's CTA barrier**: the trace before it has an event on
barrier 0. -/
theorem role_bar0 (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) :
    ∀ k {i : Role} {d : (frag p L g i).D} {n : Cls → Nat},
      Frame.stateAt (thread p L) X g k = some (some (.inr ⟨i, d⟩, n)) →
      0 < ((X.tr g).take k).countP (Execution.isBarId 0) := by
  intro k
  induction k with
  | zero =>
    intro i d n h
    rw [Frame.stateAt_zero] at h
    simp [thread, glued, Code.glue, Code.enter, Startup.code, exit] at h
  | succ k ih =>
    intro i d n h
    by_cases hk : k < (X.tr g).length
    · obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hk⟩
      rw [Frame.stateAt_succ he] at h
      cases hσ : Frame.stateAt (thread p L) X g k with
      | none => rw [hσ] at h; simp at h
      | some o =>
        cases o with
        | none => rw [hσ] at h; simp [Code.toMachine] at h
        | some σ =>
          rw [hσ] at h
          obtain ⟨σ0, n0⟩ := σ
          rcases σ0 with s | ⟨i0, d0⟩
          · change (thread p L g).next (.inl s, n0) e = some (some (.inr ⟨i, d⟩, n)) at h
            obtain ⟨h1, -⟩ := Code.counted_next_some (C := glued p L g) h
            simp only [glued, Code.glue] at h1
            cases hs : Startup.succ L g s e with
            | none => simp [Startup.code, hs] at h1
            | some o' =>
              cases o' with
              | none => simp [Startup.code, hs] at h1
              | some s' =>
                simp only [Startup.code, hs, Option.map_some, Option.some.injEq] at h1
                have hx : exit L g s' ≠ none := by
                  intro hn
                  simp [Code.enter, hn] at h1
                have hb := succ_exit_bar hs hx
                have hE := (start_fired hp hX he hσ).1
                obtain ⟨site, x1, x2, x3⟩ := s
                simp only at hb
                subst hb
                simp only [Startup.Ev] at hE
                rw [List.take_add_one, he, Option.toList_some, List.countP_append]
                obtain ⟨pc, kind⟩ := e
                simp only at hE
                subst hE
                simp [Execution.isBarId]
          · have := ih hσ
            have := countP_take_mono' (Execution.isBarId 0) (X.tr g) (show k ≤ k + 1 by omega)
            omega
    · rw [Frame.stateAt_of_le (show (X.tr g).length ≤ k + 1 by omega),
        ← Frame.stateAt_of_le (show (X.tr g).length ≤ k by omega)] at h
      have := ih h
      have := countP_take_mono' (Execution.isBarId 0) (X.tr g) (show k ≤ k + 1 by omega)
      omega

/-! ### The elected lane's path -/

open Startup in
/-- The startup sites of a lane of warp 0 that every election elects, in order. -/
def pathSite : List Startup.Site :=
  [.sh 0, .sh 1, .sh 2, .elect 0, .init 0, .init 1, .elect 1, .init 2, .init 3, .elect 2, .init 4,
    .init 5, .init 6, .elect 3, .init 7, .init 8, .init 9, .elect 4, .init 10, .init 11, .elect 5,
    .init 12, .init 13, .elect 6, .init 14, .init 15, .elect 7, .init 16, .init 17, .elect 8,
    .init 18, .init 19, .elect 9, .init 20, .init 21, .elect 10, .init 22, .init 23, .elect 11,
    .init 24, .init 25, .elect 12, .init 26, .init 27, .elect 13, .init 28, .init 29, .elect 14,
    .init 30, .init 31, .elect 15, .init 32, .init 33, .fence, .bar]

/-- The site after a site, on that lane. -/
def nextLead : Startup.Site → Startup.Site
  | .sh 0 => .sh 1
  | .sh 1 => .sh 2
  | .sh 2 => .elect 0
  | .elect j => Startup.firstInit j
  | .init n => match Startup.initSucc n with
    | .elect j => Startup.afterSite j
    | s => s
  | .fence => .bar
  | s => s

theorem path_next : ∀ k < 54, pathSite.getD (k + 1) .bar = nextLead (pathSite.getD k .bar) := by
  decide

theorem path_ne_bar : ∀ k < 54, pathSite.getD k .bar ≠ .bar := by decide

/-- The position of each initialization on the path. -/
def initPos (q : Fin 34) : Nat :=
  [4, 5, 7, 8, 10, 11, 12, 14, 15, 16, 18, 19, 21, 22, 24, 25, 27, 28, 30, 31, 33, 34, 36, 37,
    39, 40, 42, 43, 45, 46, 48, 49, 51, 52].getD q.val 0

theorem initPos_lt (q : Fin 34) : initPos q < 54 := by fin_cases q <;> decide

theorem path_initPos (q : Fin 34) : pathSite.getD (initPos q) .bar = .init q := by
  fin_cases q <;> decide

/-- **One step of the elected lane**: from a site before the barrier the startup moves to the
next site of the path, given that the warp word is `0` (at every site after the shuffles) and
that the elections elect the lane. -/
theorem succ_lead {s s' : Startup.D} {e : Event} (h : Startup.succ L g s e = some (some s'))
    (hb : s.site ≠ .bar) (h3 : s.site.mid = true → s.x3 = 0)
    (h3' : s'.site.mid = true → s'.x3 = 0)
    (hld : ∀ jj, s.site = .elect jj → ∀ mk inst ld, e.kind = .elect mk inst ld →
      ld = laneOf L g) :
    s'.site = nextLead s.site := by
  obtain ⟨site, x1, x2, x3⟩ := s
  cases site with
  | bar => exact absurd rfl hb
  | enter r => simp [Startup.succ] at h
  | fence =>
    simp only [Startup.succ, Option.some.injEq] at h
    subst h
    rfl
  | elect j =>
    have hx3 := h3 rfl
    simp only at hx3
    subst hx3
    simp only [Startup.succ] at h
    split at h
    · rename_i mk inst ld hk
      simp only [Option.some.injEq] at h
      subst h
      simp only [hld j rfl mk inst ld hk, ↓reduceIte]
      rfl
    · simp at h
  | init q =>
    have hx3 := h3 rfl
    simp only at hx3
    subst hx3
    simp only [Startup.succ] at h
    split at h
    · rename_i jj hjj
      simp only [Option.some.injEq] at h
      subst h
      simp only [nextLead, hjj, Startup.afterBlock]
      split_ifs with h0
      · exact absurd h0 (by decide)
      · rfl
    · rename_i hne
      simp only [Option.some.injEq] at h
      subst h
      simp only [nextLead]
  | sh j =>
    simp only [Startup.succ] at h
    split at h
    · simp only [Startup.word32] at h
      split at h
      · rename_i x _
        simp only [Option.some.injEq] at h
        subst h
        fin_cases j
        · rfl
        · rfl
        · simp only at h3' ⊢
          split_ifs with hne
          · exfalso
            have := h3' (by simp [hne, Startup.Site.mid])
            simp only [hne, ↓reduceIte] at this
            subst this
            revert hne
            decide
          · rfl
      · simp at h
    · simp at h

/-- **The elected lane walks the path**: a lane of warp 0 whose elections before position `K`
elect it, with no event on the CTA barrier before `K` and an event at `K` that is no undefined
behaviour, is at the `k`-th site of the path at every position `k ≤ K ≤ 54`. -/
theorem lead_path (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {ℓ K : Nat}
    (hℓ : InWarp L 0 ℓ) (hK : K ≤ 54) {eK : Event} (heK : X.get (ℓ, K) = some eK)
    (hub : ∀ f, eK.kind ≠ .ub f)
    (hb : ((X.tr ℓ).take K).countP (Execution.isBarId 0) = 0)
    (hlead : ∀ j < K, (∃ jj, pathSite.getD j .bar = .elect jj) →
      ∀ pc inst ld, X.get (ℓ, j) = some ⟨pc, .elect (2 ^ 32 - 1) inst ld⟩ → ld = laneOf L ℓ) :
    ∀ k ≤ K, ∃ s n, Frame.stateAt (thread p L) X ℓ k = some (some (.inl s, n)) ∧
      s.site = pathSite.getD k .bar ∧ StartAt0 L s n := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨⟨.sh 0, 0, 0, 0⟩, fun _ => 0, Frame.stateAt_zero, rfl,
      (start0Ref_init (p := p) (L := L) (g := ℓ)).1⟩
  | succ k ih =>
    intro hk1
    obtain ⟨s, n, hσ, hsite, hS⟩ := ih (by omega)
    have hKl : K < (X.tr ℓ).length := (List.getElem?_eq_some_iff.mp heK).1
    have hcount : ((X.tr ℓ).take (k + 1)).countP (Execution.isBarId 0) = 0 := by
      have := countP_take_mono' (Execution.isBarId 0) (X.tr ℓ) hk1
      omega
    obtain ⟨hF, hI⟩ := start0_state hp hX hℓ (k + 1) hcount
    obtain ⟨e, he⟩ : ∃ e, X.get (ℓ, k) = some e :=
      ⟨_, List.getElem?_eq_getElem (show k < (X.tr ℓ).length by omega)⟩
    -- the state after the event is alive
    obtain ⟨e1, he1⟩ : ∃ e, X.get (ℓ, k + 1) = some e :=
      ⟨_, List.getElem?_eq_getElem (show k + 1 < (X.tr ℓ).length by omega)⟩
    have hub1 : ∀ pc f, e1 ≠ ⟨pc, .ub f⟩ := by
      rintro pc f rfl
      by_cases hkK : k + 1 = K
      · subst hkK
        rw [he1] at heK
        cases heK
        exact hub f rfl
      · have := ub_last hX he1 heK
        omega
    obtain ⟨σ, hσ1⟩ : ∃ σ, Frame.stateAt (thread p L) X ℓ (k + 1) = some σ := by
      rcases Frame.firedU (fun g hg => thread_sound hp hg) hX he1 with ⟨σ, o, h, -⟩ |
        ⟨-, pc, f, h⟩
      · exact ⟨σ, h⟩
      · exact absurd h (hub1 pc f)
    cases σ with
    | none => exact absurd hσ1 hF.1
    | some σ =>
      obtain ⟨s', hs'⟩ := hI σ hσ1
      have hJ := hF.2 σ hσ1
      obtain ⟨σ1, n'⟩ := σ
      simp only at hs'
      subst hs'
      have hS' : StartAt0 L s' n' := hJ.1
      have hstep : (thread p L ℓ).next (.inl s, n) e = some (some (.inl s', n')) := by
        have := Frame.stateAt_succ (C := thread p L) (show (X.tr ℓ)[k]? = some e from he)
        rw [hσ, hσ1] at this
        exact this.symm
      obtain ⟨h1, -⟩ := Code.counted_next_some (C := glued p L ℓ) hstep
      simp only [glued, Code.glue] at h1
      cases hsu : Startup.succ L ℓ s e with
      | none => simp [Startup.code, hsu] at h1
      | some o' =>
        cases o' with
        | none => simp [Startup.code, hsu] at h1
        | some s0 =>
          simp only [Startup.code, hsu, Option.map_some, Option.some.injEq] at h1
          have hs0 : s0 = s' := by
            unfold Code.enter at h1
            split at h1
            · cases h1
            · cases h1; rfl
          subst hs0
          refine ⟨s0, n', hσ1, ?_, hS'⟩
          have hk54 : k < 54 := by omega
          rw [path_next k hk54, ← hsite]
          refine succ_lead hsu (hsite ▸ path_ne_bar k hk54)
            (fun hm => (startAt0_of_mid hm hS).2.2) (fun hm => (startAt0_of_mid hm hS').2.2)
            (fun jj hjj mk inst ld hk => ?_)
          have hE := (start_fired hp hX he hσ).1
          obtain ⟨pc, kind⟩ := e
          simp only at hk
          subst hk
          simp only [Startup.Ev, hjj] at hE
          rcases hE with ⟨inst', ld', -, hk'⟩ | ⟨f, hk'⟩
          · simp only [Kind.elect.injEq] at hk'
            obtain ⟨rfl, rfl, rfl⟩ := hk'
            exact hlead k (by omega) ⟨jj, hsite.symm.trans hjj⟩ pc inst ld he
          · cases hk'

end
end PTX.Kernels.TmlFa4Fwd.Proof
