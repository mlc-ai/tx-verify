-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Machine
public import Kernels.TmlFa4Fwd.Proof.Loader.Shape

@[expose] public section

/-! # The loader warps' row-address words keep a 16-byte pattern

A packet's address load records the low word of a row's global address (`l0`, sub-step 0 of
`lw`) and the row shuffle the low word of the row it copies (`x0`, at `xl`). The `cp.async`
copies read 16 bytes from that address, so they need it to be a multiple of 16. `AOk` is the
pattern both words keep: a multiple of 16. No step but those two changes them (`succ_aok`), so the
pattern holds along the trace once the loaded and the received words have it (`Top/LdAddrTrace`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {g w : Nat}

/-- **The row-address words of a state are multiples of 16.** -/
def AOk (v : V) : Prop := v.l0.toNat % 16 = 0 ∧ v.x0.toNat % 16 = 0

/-- A successor that keeps both row-address words. -/
def KeepA (d d' : D) : Prop := d'.v.l0 = d.v.l0 ∧ d'.v.x0 = d.v.x0

theorem aok_of {d d' : D} (h : AOk d.v) (hk : KeepA d d') : AOk d'.v := by
  unfold AOk; rw [hk.1, hk.2]; exact h

theorem keepA_ite {c : Bool} {d a b : D} (ha : KeepA d a) (hb : KeepA d b) :
    KeepA d (D.ite c a b) := by
  cases c <;> assumption

theorem keepA_iteS {c : Bool} {d a b : D} (ha : KeepA d a) (hb : KeepA d b) :
    KeepA d (D.iteS c a b) := by
  cases c
  · exact ⟨hb.1, hb.2⟩
  · exact ⟨ha.1, ha.2⟩

theorem keepA_scanExit {d d0 : D} (h : KeepA d d0) (late : Bool) (gx cur : BitVec 64) :
    KeepA d (scanExit p late d0 gx cur) := by
  unfold scanExit
  apply keepA_ite <;> cases late <;> exact ⟨h.1, h.2⟩

theorem keepA_loopHead {d d0 : D} (h : KeepA d d0) (late : Bool) (grp acc : BitVec 64) :
    KeepA d (loopHead p L g late d0 grp acc) := by
  unfold loopHead
  apply keepA_ite
  · exact keepA_scanExit h _ _ _
  · apply keepA_ite <;> exact ⟨h.1, h.2⟩

theorem keepA_afterTotal (k : Epilogue.Scan) (d : D) (x : BitVec 64) :
    KeepA d (afterTotal p L g k d x) := by
  unfold afterTotal
  cases k <;> dsimp only <;> apply keepA_ite <;>
    first
      | (refine keepA_scanExit ?_ _ _ _; exact ⟨rfl, rfl⟩)
      | (refine keepA_loopHead ?_ _ _ _; exact ⟨rfl, rfl⟩)

theorem keepA_afterTiles {d d' : D} {x : BitVec 64} (h : afterTiles p L g d x = some d') :
    KeepA d d' := by
  simp only [afterTiles] at h
  split_ifs at h with h1 h2
  simp only [Option.some.injEq] at h
  subst h
  apply keepA_ite <;> exact ⟨rfl, rfl⟩

theorem keepA_passStart {d d0 : D} (h : KeepA d d0) (late : Bool) :
    KeepA d (passStart p L g late d0) := by
  unfold passStart; apply keepA_ite <;> exact ⟨h.1, h.2⟩

theorem keepA_pgEnter {d d0 : D} (h : KeepA d d0) (per : Per) (it : Fin 2) :
    KeepA d (pgEnter p L g d0 per it) := by
  unfold pgEnter; apply keepA_iteS <;> exact ⟨h.1, h.2⟩

theorem keepA_afterTail {d d0 : D} (h : KeepA d d0) : KeepA d (afterTail p L g d0) := by
  unfold afterTail
  apply keepA_iteS
  · (refine keepA_passStart ?_ _; exact ⟨h.1, h.2⟩)
  · (refine keepA_pgEnter ?_ _ _; exact ⟨h.1, h.2⟩)

theorem keepA_afterWarm {d d0 : D} (h : KeepA d d0) : KeepA d (afterWarm p L g w d0) := by
  unfold afterWarm
  apply keepA_iteS
  · exact keepA_afterTail h
  · exact ⟨h.1, h.2⟩

theorem keepA_afterPrime {d d0 : D} (h : KeepA d d0) : KeepA d (afterPrime p L g w d0) := by
  unfold afterPrime
  apply keepA_iteS
  · (refine keepA_afterWarm ?_; exact ⟨h.1, h.2⟩)
  · (refine keepA_pgEnter ?_ _ _; exact ⟨h.1, h.2⟩)

theorem keepA_warmEnd {d d0 : D} (h : KeepA d d0) : KeepA d (warmEnd p L g w d0) := by
  unfold warmEnd
  apply keepA_iteS
  · (refine keepA_pgEnter ?_ _ _; exact ⟨h.1, h.2⟩)
  · (refine keepA_afterWarm ?_; exact ⟨h.1, h.2⟩)

theorem keepA_steadyEnd {d d0 : D} (h : KeepA d d0) : KeepA d (steadyEnd p L g d0) := by
  unfold steadyEnd
  apply keepA_iteS
  · (refine keepA_pgEnter ?_ _ _; exact ⟨h.1, h.2⟩)
  · (refine keepA_passStart ?_ _; exact ⟨h.1, h.2⟩)

theorem keepA_afterArrive (d : D) (per : Per) (b : Bool) :
    KeepA d (afterArrive p L g w d per b) := by
  cases per <;> cases b <;> simp only [afterArrive]
  · apply keepA_ite <;> exact ⟨rfl, rfl⟩
  · (refine keepA_afterPrime ?_; exact ⟨rfl, rfl⟩)
  · apply keepA_ite <;> exact ⟨rfl, rfl⟩
  · (refine keepA_warmEnd ?_; exact ⟨rfl, rfl⟩)
  · exact ⟨rfl, rfl⟩
  · (refine keepA_steadyEnd ?_; exact ⟨rfl, rfl⟩)

theorem keepA_groupEnd {d d0 : D} (h : KeepA d d0) (t : Fin 7) :
    KeepA d (groupEnd p L g d0 t) := by
  fin_cases t <;> simp only [groupEnd] <;> first | exact ⟨h.1, h.2⟩ | exact keepA_afterTail h

theorem keepA_teNext (d : D) (t : Fin 7) (i : Fin 3) : KeepA d (teNext p L g d t i) := by
  fin_cases i <;> simp only [teNext]
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · split
    · (refine keepA_groupEnd ?_ _; exact ⟨rfl, rfl⟩)
    · (refine keepA_groupEnd ?_ _; exact ⟨rfl, rfl⟩)

theorem keepA_teElected (d : D) (t : Fin 7) (i : Fin 3) : KeepA d (teElected d t i) := by
  fin_cases i <;> simp only [teElected] <;> first | exact ⟨rfl, rfl⟩ | (split <;> exact ⟨rfl, rfl⟩)

theorem keepA_dwNext (d : D) (k : Fin 3) : KeepA d (dwNext w d k) := by
  fin_cases k <;> simp only [dwNext] <;>
    first | exact ⟨rfl, rfl⟩ | (apply keepA_ite <;> exact ⟨rfl, rfl⟩)

theorem keepA_pkStart (d : D) (per : Per) (b : Bool) : KeepA d (pkStart L g d per b) := by
  unfold pkStart; repeat' split
  all_goals exact ⟨rfl, rfl⟩

theorem keepA_word32 {v : Value} {f : BitVec 64 → D} {d d' : D} (hf : ∀ x, KeepA d (f x))
    (h : word32 v f = some (some d')) : KeepA d d' := by
  unfold word32 at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; exact hf _
  · simp at h

/-- A successor that keeps the row-address words: a state with the same words, or one of the
machine's composite successors. -/
syntax "ka_leaf" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| ka_leaf) => `(tactic| first
      | exact ⟨rfl, rfl⟩
      | (refine keepA_passStart ?_ _; exact ⟨rfl, rfl⟩)
      | exact keepA_afterArrive _ _ _
      | exact keepA_afterTotal _ _ _
      | (refine keepA_groupEnd ?_ _; exact ⟨rfl, rfl⟩)
      | exact keepA_pkStart _ _ _
      | (refine keepA_pgEnter ?_ _ _; exact ⟨rfl, rfl⟩)
      | exact keepA_teElected _ _ _
      | exact keepA_teNext _ _ _
      | exact keepA_dwNext _ _
      | (apply keepA_ite <;> ka_leaf)
      | (split <;> ka_leaf))

/-- The successor of an event that returns a value. -/
syntax "ka_kind" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| ka_kind) => `(tactic| first
      | (simp only [Option.some.injEq] at hn; subst hn; ka_leaf)
      | exact keepA_word32 (fun _ => by ka_leaf) hn
      | (obtain ⟨d1, hd1, h1⟩ := Option.map_eq_some_iff.mp hn
         simp only [Option.some.injEq] at h1
         subst h1
         exact keepA_afterTiles hd1)
      | (split at hn <;> ka_kind)
      | (simp at hn; done))

set_option maxHeartbeats 4000000 in
/-- **A step keeps the row-address pattern** when the word an address load records at sub-step 0
and the word a row shuffle receives have it. -/
theorem succ_aok {d d' : D} {e : Event} (h : AOk d.v)
    (hlw : ∀ per b hh a bs x, d.site = .lw per b hh → d.k = 0 → e.kind = .rd a bs →
      rebuild 3 bs = .ok (.bits 32 x) → x.toNat % 16 = 0)
    (hxl : ∀ per b i md a bb c x o, d.site = .xl per b i →
      e.kind = .shfl md a bb c (.bits 32 x) o → x.toNat % 16 = 0)
    (hn : succ p L g w d e = some (some d')) : AOk d'.v := by
  obtain ⟨s, v, kk⟩ := d
  obtain ⟨pc, kind⟩ := e
  cases s
  case lw per b hh =>
    simp only [succ] at hn
    cases kind <;> simp only [reduceCtorEq] at hn
    rename_i a bs
    split at hn
    · rename_i y hy
      unfold word32 at hn
      split at hn
      · rename_i x
        simp only [Option.some.injEq] at hn
        split at hn
        · subst hn
          exact ⟨hlw per b hh a bs x rfl (Fin.ext (by assumption)) rfl hy, h.2⟩
        · subst hn; exact h
      · simp at hn
    · simp at hn
  case xl per b i =>
    simp only [succ] at hn
    cases kind <;> simp only [reduceCtorEq] at hn
    rename_i md a bb c x o
    unfold word32 at hn
    split at hn
    · rename_i y
      simp only [Option.some.injEq] at hn
      subst hn
      exact ⟨h.1, hxl per b i md a bb c y o rfl rfl⟩
    · simp at hn
  all_goals refine aok_of h ?_
  all_goals simp only [succ] at hn
  all_goals ka_kind

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
