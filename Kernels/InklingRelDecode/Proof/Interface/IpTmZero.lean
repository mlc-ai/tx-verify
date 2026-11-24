-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.IpTmOps
public import Kernels.InklingRelDecode.Proof.Interface.Reach
public import Kernels.InklingRelDecode.Proof.Interface.ShapeWords
public import Lemmas.Flow.AllocTmpl

@[expose] public section

/-!
# The Tensor Memory base word along a default-partition thread

The common start's load of the base word (`DStart.Site.ld0`) puts the word it reads into the
state (`DStart.D.tm`); the prologue carries it as `ProA.Inh.tm`, the softmax region as `Sm.Ent.tm`
(`Sm.D.e.tm`) and the epilogue as `Epi.Prm.tm`, the column the deallocation frees. If every
four-byte read of the base word returns the 32-bit zero (`BaseWordRead`, the premise
`SO.BaseWordZero`), the word is 0 at every state after the load (`TmZ`, `tmz_inv`). So:

* `smBaseZero_of`: every softmax state's `Sm.D.e.tm` is 0 (`Rs.SmBaseZero`);
* `dealloc_zero`: every deallocation names column 0 (`Tmem1Facts.dealloc`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The base word a state holds is 0** (after the load of the common start). -/
def TmZ : TSt → Prop
  | .d (.dstart d) => (d.site = .bar1 ∨ d.site = .relinq ∨ d.site = .shfl ∨ d.site = .toProA) →
      d.w = b32 0
  | .d (.pro d) => d.dt.pro.tm = 0 ∧ d.dt.w = b32 0
  | .d (.sm d) => d.e.tm = 0
  | .d (.epi d) => d.pr.tm = 0
  | .w _ => True

theorem tmz_dstart {g : Nat} {site : DStart.Site} {tm : Value} {e : Event} {a : DComp.St}
    (hz : ∀ a bs, site = .ld0 → e.kind = .rd a bs → bs = (b32 0).toBytes.map some)
    (h : TmZ (.d (.dstart ⟨site, tm⟩)))
    (ha : DComp.next L g Q (.dstart ⟨site, tm⟩) e = some (some a)) : TmZ (.d a) := by
  change DComp.dstartNext L g Q ⟨site, tm⟩ e = some (some a) at ha
  cases site
  · by_cases hl : laneOf L g = 0 <;>
      simp [DComp.dstartNext, DStart.next, hl] at ha <;> subst ha <;> simp [TmZ]
  · simp [DComp.dstartNext, DStart.next] at ha
    subst ha
    simp [TmZ]
  · simp [DComp.dstartNext, DStart.next] at ha
    subst ha
    simp [TmZ]
  · obtain ⟨pc, kd⟩ := e
    cases kd <;> simp [DComp.dstartNext, DStart.next] at ha
    rename_i a' bs
    have hb := hz a' bs rfl rfl
    subst hb
    simp only [rebuild_b32] at ha
    obtain ⟨a1, h1, ha⟩ := ha
    obtain rfl := Option.some.inj (Option.some.inj h1)
    simp only [reduceCtorEq, ↓reduceIte] at ha
    subst ha
    simp [TmZ]
  · have h0 : tm = b32 0 := h (.inl rfl)
    subst h0
    by_cases hl : g % L.block < 32 <;>
      simp [DComp.dstartNext, DStart.next, hl] at ha <;> subst ha <;> simp [TmZ]
  · have h0 : tm = b32 0 := h (.inr (.inl rfl))
    subst h0
    simp [DComp.dstartNext, DStart.next] at ha
    subst ha
    simp [TmZ]
  · have h0 : tm = b32 0 := h (.inr (.inr (.inl rfl)))
    subst h0
    simp [DComp.dstartNext, DStart.next] at ha
    obtain ⟨a', ha', rfl⟩ := ha
    have hb : a'.site = DStart.Site.toProA ∧ a'.w = b32 0 := by
      repeat' split at ha'
      all_goals first
        | (simp at ha'; done)
        | (simp only [Option.some.injEq] at ha'; subst ha'; exact ⟨rfl, rfl⟩)
    obtain ⟨hb1, hb2⟩ := hb
    simp [hb1, TmZ, ProA.D.start, ProA.Dat.start, DStart.inh, hb2, ProA.shW, Raw.word32Of_b32]
  · simp [DComp.dstartNext, DStart.next] at ha

/-- **A step keeps the base word 0**, when the event of the load of the base word reads the
zero word. -/
theorem tmz_next {g : Nat} {s s' : TSt} {e : Event}
    (hz : ∀ (tm : Value) a bs, s = .d (.dstart ⟨.ld0, tm⟩) → e.kind = .rd a bs →
      bs = (b32 0).toBytes.map some)
    (h : TmZ s) (hn : (threadCode L g Q).next s e = some (some s')) : TmZ s' := by
  cases s with
  | w s =>
    obtain ⟨a, -, rfl⟩ := map_map_eq_some_some (show (WComp.next L g s e).map
      (Option.map TSt.w) = some (some s') from hn)
    trivial
  | d s =>
    obtain ⟨a, ha, rfl⟩ := map_map_eq_some_some (show (DComp.next L g Q s e).map
      (Option.map TSt.d) = some (some s') from hn)
    cases s with
    | dstart d =>
      obtain ⟨site, tm⟩ := d
      exact tmz_dstart (fun a bs hs hk => hz tm a bs (by rw [hs]) hk) h ha
    | pro d =>
      change DComp.proNext L g Q d e = some (some a) at ha
      unfold DComp.proNext at ha
      split at ha
      · split at ha
        · simp only [Option.some.injEq] at ha
          subst ha
          exact h.1
        · cases ha
      · obtain ⟨a', ha', rfl⟩ := map_map_eq_some_some ha
        show a'.dt.pro.tm = 0 ∧ a'.dt.w = b32 0
        rw [DComp.next_pro ha', DComp.next_w ha']
        exact h
    | sm d =>
      change DComp.smNext L g d e = some (some a) at ha
      unfold DComp.smNext at ha
      split at ha
      · unfold DComp.exitNext at ha
        split at ha
        · simp only [Option.some.injEq] at ha
          subst ha
          show (if _ then _ else _ : Epi.D).pr.tm = 0
          split <;> exact h
        · cases ha
      · obtain ⟨a', ha', rfl⟩ := map_map_eq_some_some ha
        show a'.e.tm = 0
        rw [sm_next_e ha']
        exact h
    | epi d =>
      obtain ⟨a', ha', rfl⟩ := map_map_eq_some_some (show (Epi.next d e).map
        (Option.map DComp.St.epi) = some (some a) from ha)
      show a'.pr.tm = 0
      rw [epi_next_pr ha']
      exact h

theorem tmz_init {g : Nat} : TmZ (code L Q g).init := by
  show TmZ (if g % L.block < 128 then TSt.d (DComp.code L g Q).init
    else .w (WComp.code L g Q).init)
  split_ifs
  · show TmZ (.d (.dstart (DStart.D.start L g)))
    unfold DStart.D.start
    split_ifs <;> simp [TmZ]
  · trivial

/-- **The base word is 0 at every state of a thread**, if every read of the base word returns the
zero word (`BaseWordRead`). -/
theorem tmz_inv (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hb : BaseWordRead L X) {g : Nat} (hg : g < L.threads) :
    ∀ k s, k ≤ (X.tr g).length → St Q L X g k = some (some s) → TmZ s := by
  intro k
  induction k with
  | zero =>
    intro s _ hs
    have hs : Frame.stateAt (code L Q) X g 0 = some (some s) := hs
    rw [Frame.stateAt_zero] at hs
    have hs' : s = (threadCode L g Q).init := (Option.some.inj (Option.some.inj hs)).symm
    subst hs'
    exact tmz_init
  | succ k ih =>
    intro s' hk hs'
    have hs' : Frame.stateAt (code L Q) X g (k + 1) = some (some s') := hs'
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [Frame.stateAt_succ he] at hs'
    cases hσ : Frame.stateAt (code L Q) X g k with
    | none => rw [hσ] at hs'; simp at hs'
    | some o =>
      cases o with
      | none => rw [hσ] at hs'; simp [Flow.Code.toMachine] at hs'
      | some s =>
        rw [hσ] at hs'
        simp only [Option.bind_some] at hs'
        have hn : (threadCode L g Q).next s e = some (some s') := hs'
        refine tmz_next (fun tm a bs hs hk' => ?_) (ih s (by omega) hσ) hn
        subst hs
        obtain ⟨pc, kd⟩ := e
        simp only at hk'
        subst hk'
        have hget : X.get (g, k) = some ⟨pc, .rd a bs⟩ := he
        obtain ⟨u, hF⟩ := fired_cont hX hf hg hget hσ (by simp [ExitState])
        obtain ⟨ac, bs', he2, hl, hz, -⟩ := DStart.shape_ld0 (ProA.sharedOk_of_pre hpre)
          (fired_dstart hF) rfl
        simp only [Event.mk.injEq, Kind.rd.injEq] at he2
        obtain ⟨-, rfl, rfl⟩ := he2
        exact hb hget hl hz

/-- **`Rs.SmBaseZero`**: every softmax state's Tensor Memory base is 0. -/
theorem smBaseZero_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hb : BaseWordRead L X) :
    ∀ {g k : Nat} {d : Sm.D}, g < L.threads → St Q L X g k = some (some (.d (.sm d))) →
      d.e.tm = 0 := by
  intro g k d hg hσ
  by_cases hk : k ≤ (X.tr g).length
  · exact tmz_inv hpre hX hf hb hg k _ hk hσ
  · have h2 : St Q L X g (X.tr g).length = some (some (.d (.sm d))) :=
      (Frame.stateAt_of_le (C := code L Q) (X := X) (g := g) (k := k) (by omega)).symm.trans hσ
    exact tmz_inv hpre hX hf hb hg _ _ le_rfl h2

/-- **A deallocation frees column 0** (`Tmem1Facts.dealloc`), if every read of the base word
returns the zero word. -/
theorem dealloc_zero (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hb : BaseWordRead L X) {g k pc : Nat} {grp : CtaGroup}
    {dst : Option Loc} {a n : Nat} (hg : g < L.threads)
    (he : X.get (g, k) = some ⟨pc, .tc (.resource grp dst (.dealloc a n))⟩) : a = 0 := by
  obtain ⟨-, h⟩ := res_event_state hpre hX hf he
  rcases h with ⟨tm, -, -, h⟩ | ⟨tm, -, -, h⟩ | ⟨d, hσ, -, -, h⟩
  · cases h
  · cases h
  · simp only [Tmem.Request.dealloc.injEq] at h
    rw [h.1]
    exact tmz_inv hpre hX hf hb hg k _ (ev_le he) hσ

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
