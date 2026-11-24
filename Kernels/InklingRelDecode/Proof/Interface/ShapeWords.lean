-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.ShapeMma
public import Kernels.InklingRelDecode.Proof.Thread.ShapeBaseWord
public import Lemmas.Flow.AllocTmpl

@[expose] public section

/-!
# The words the MMA warp read

`MmaWords` (`Result/MmaPremises.lean`) says the MMA warp's loop bound is the split's `num_iters`
and its Tensor Memory base is column 0. The thread layer proves what the abstract state does with
the two words the warp reads, and takes the two reads-from facts as premises (the protocol layer
proves them from the prologue's stores and the `bar.sync` that follows them):

* `BaseWordRead`: a four-byte read of the base word `global_smem + 0` returns the 32-bit zero
  (the premise `SO.BaseWordZero`);
* `NumWordRead`: a four-byte read of `global_smem + 212996` returns the 32-bit `num_iters` of the
  reading thread's CTA.

`worker_ld0_shape` is the event shape of the worker's read of the base word (four bytes at
`global_smem + 0` of the thread's CTA), which `BaseWordRead` needs. `words_after` is the invariant
along the run: every state of the worker machine after the base word was read carries the zero
word, and an MMA state past its read of `num_iters` carries it.

`MmaWords.iters` as written for every MMA state is false at the two sites before the read of
`num_iters` (`setMaxReg`, `ldNum`: `d.n = 0` there), so `mma_iters` takes `d.site` past them; the
consumer (`Result/MmaOperand.lean`) uses the field only at a QK or PV site.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {X : Execution}

/-! ### Induction along the trace -/

/-- **Forward induction along a thread's trace.** A property of the thread's states that holds at
the first state and is kept by each step along an event of the trace holds at every state. -/
theorem stateAt_induction (Pr : TSt → Prop) (h0 : Pr (code L Q g).init)
    (hstep : ∀ (k : Nat) (e : Event) (s s' : TSt), (X.tr g)[k]? = some e →
      St Q L X g k = some (some s) → Pr s → (threadCode L g Q).next s e = some (some s') →
      Pr s') :
    ∀ (k : Nat) (s : TSt), St Q L X g k = some (some s) → Pr s := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro s hs
    by_cases hi : s = (code L Q g).init
    · rw [hi]
      exact h0
    · obtain ⟨k0, e, s0, hlt, he, hs0, hn⟩ := stateAt_pred hs hi
      exact hstep k0 e s0 s he hs0 (ih k0 hlt s0 hs0) hn

/-! ### The worker's read of the base word -/

/-- **The worker's read of the Tensor Memory base word.** Four bytes at `global_smem` of the
thread's CTA. -/
theorem worker_ld0_shape (hpre : Pre Q L mem0) {w : Worker.D} {e : Event} {u : TState}
    (hs : w.site = .ld0)
    (hF : (WComp.code L g Q).toMachine.Fired (some (.worker w)) e (some u)) :
    ∃ pc ac bs, e = ⟨pc, .rd ac bs⟩ ∧ ac.loc = ⟨.shared, g / L.block, L.sharedBase⟩ ∧
      ac.size = 4 := by
  obtain ⟨t, hgood, hfire⟩ := hF
  obtain ⟨hat, hinv⟩ := hgood
  have hinv' : (WComp.code L g Q).inv (.worker w) := hinv
  obtain ⟨ins, hc, -, -⟩ := (WComp.stepAt hpre (.worker w)).site hinv'
  have hpc : Worker.Site.pc w.site = 13 := by rw [hs]; rfl
  have hc' : kernel.code[13]? = some ins := by
    have hc1 : kernel.code[WComp.pc (WComp.WSt.worker w)]? = some ins := hc
    simpa [WComp.pc, hpc] using hc1
  have hf : Fires 13 (eventTmpl Loader.asms L g t ins.op) e (some u) := by
    have := hfire
    simp only [Code.toMachine, Code.tmpl] at this
    have hat' : t.pc = 13 := by
      have : t.pc = w.site.pc := hat.1
      rw [this, hpc]
    rw [hat'] at this
    have hc2 : kernel.code[WComp.pc (WComp.WSt.worker w)]? = some ins := hc
    rw [hc2] at this
    exact this
  obtain ⟨a, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10⟩ : ∃ a : MemAccess,
      kernel.code[13]? = some ⟨none, .mem a⟩ ∧ a.rule = some .threadAccess ∧
      a.addr.base = .sharedSym 0 ∧ a.addr.off = ((0 : Nat) : Int) ∧ a.kind = .load ∧
      a.nc = false ∧ a.space = some (.shared .cta) ∧ a.sem = .weak ∧
      (a.nc || a.hints.globalOnly || a.vec == 8 || (a.vec == 4 && a.elem.width == 64)) = false ∧
      a.elem.width = 32 :=
    ⟨_, Flow.code_13, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain rfl := Option.some.inj (hc'.symm.trans ha1)
  have h1 : L.sharedBase + 0 + 0 < 2 ^ 32 := by
    have := (EvW.mmEnv_of_pre hpre).sb
    omega
  obtain ⟨ac, bs, he, hl, hsz, hel⟩ := EvW.fires_ldv_sharedSym ha2 ha3 ha4 ha5 ha6 ha7 ha8 ha9
    ha10 h1 hf
  have hsub : t.sub = 0 := by
    have : t.sub = WComp.sub (.worker w) := hat.2.1
    simpa [WComp.sub] using this
  rw [hsub] at hl
  exact ⟨13, ac, bs, he, by simpa using hl, hsz⟩

/-! ### The two words -/

/-- **The base word's read** returns the 32-bit zero: a four-byte read of `global_smem + 0` (the
premise `SO.BaseWordZero`, from the prologue's allocation store and the `bar.sync 0` before the
read). -/
def BaseWordRead (L : Launch) (X : Execution) : Prop :=
  ∀ {g k pc : Nat} {a : Acc} {bs : List (Option Byte)},
    X.get (g, k) = some ⟨pc, .rd a bs⟩ → a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ →
      a.size = 4 → bs = (b32 0).toBytes.map some

/-- The states whose read is of the `num_iters` word the prologue stored: the loader's read of
`num_iters` (`Loader.Site.ld1`) and the MMA warp's (`Mma.Site.ldNum`). The softmax region's
min-exchange scratch (`Sm.Site.ldL`) also reads four bytes at `global_smem + 212996` for a thread
with `tid % 4 = 1`, and returns warp 1's minimum. -/
def NumReader : TSt → Prop
  | .w (.loader d _) => d.site = .ld1
  | .w (.mma d _) => d.site = .ldNum
  | _ => False

/-- **The `num_iters` word's read** returns the 32-bit `num_iters` of the reading thread's CTA: a
four-byte read of `global_smem + 212996` by the loader's `ld1` or the MMA warp's `ldNum` (the
prologue's `st9_1` store, `EvD.st9_values`, and the `bar.sync 1` before the read). -/
def NumWordRead (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k pc : Nat} {a : Acc} {bs : List (Option Byte)} {s : TSt},
    X.get (g, k) = some ⟨pc, .rd a bs⟩ → St Q L X g k = some (some s) → NumReader s →
      a.loc = ⟨.shared, g / L.block, L.sharedBase + 212996⟩ → a.size = 4 →
      bs = (b32 (Q.numIters (ProA.cta L g .z) (ProA.cta L g .x))).toBytes.map some

theorem numIters_lt (hpre : Pre Q L mem0) {g : Nat} (hg : g < L.threads) :
    Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) < 2 ^ 32 := by
  obtain ⟨-, -, hz⟩ := ProA.cta_lt hpre hg
  have h1 := SmEntry.iters_lt Q (ProA.cta L g .z) (ProA.cta L g .x) hpre.splitsPos
  have h2 := hpre.seqRange _ hz
  unfold Params.blocks at h1
  omega

/-! ### The invariant -/

/-- What every state of a thread keeps about the two words: a worker state past the read of the
base word holds the zero word in `%r2`; an MMA state has Tensor Memory base 0, and past its read
of `num_iters` the loop bound is the CTA's `num_iters`, which is also the word the machine keeps
as loaded (`Mma.numWord`). -/
def WordsInv (Q : Params) (L : Launch) (g : Nat) : TSt → Prop
  | .d _ => True
  | .w (.worker w) => w.site = .bar0 ∨ w.site = .ld0 ∨ w.P.baseWord = b32 0
  | .w (.idle d) => d.P.baseWord = b32 0
  | .w (.loader _ P) => P.baseWord = b32 0
  | .w (.mma d P) => P.baseWord = b32 0 ∧ d.tm = 0 ∧ (d.site ≠ .setMaxReg → d.site ≠ .ldNum →
      d.n = Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) ∧
      Mma.numWord d = b32 (Q.numIters (ProA.cta L g .z) (ProA.cta L g .x)))
  | .w (.exit x) => x.P.baseWord = b32 0

/-- The MMA machine keeps the loop bound and the loaded word except at the read that sets them. -/
theorem mma_next_n {d d' : Mma.D} {e : Event} (h : Mma.next L g d e = some (some d'))
    (hs : d.site ≠ .ldNum) : d'.n = d.n ∧ d'.pro = d.pro := by
  unfold Mma.next Mma.start Mma.afterQk Mma.iterNext Mma.qkNext Mma.pvNext at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, reduceCtorEq] at h; done)
    | (simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩)
    | simp_all

/-- The worker's successor keeps the inherited registers, except at the read of the base word and
the dispatch. -/
theorem worker_next_P {w w' : Worker.D} {e : Event} (h : Worker.next L g w e = some (some w'))
    (h1 : w.site ≠ .ld0) (h2 : w.site ≠ .ldRole) : w'.P = w.P := by
  obtain ⟨site, P⟩ := w
  cases site <;> simp only [Worker.next] at h
  all_goals first
    | exact absurd rfl h1
    | exact absurd rfl h2
    | (repeat' split at h
       all_goals first
         | (simp only [Option.some.injEq, reduceCtorEq] at h; done)
         | (simp only [Option.some.injEq] at h; subst h; rfl))

/-! ### The step -/


/-- The worker's own step keeps the base word (it sets it at the read, from the premise). -/
theorem words_worker (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hb : BaseWordRead L X) {g k : Nat} {e : Event}
    {w w' : Worker.D} (he : X.get (g, k) = some e) (hg : g < L.threads) (hs : w.site ≠ .ldRole)
    (hσ : St Q L X g k = some (some (.w (.worker w))))
    (hi : w.site = .bar0 ∨ w.site = .ld0 ∨ w.P.baseWord = b32 0)
    (h : Worker.next L g w e = some (some w')) :
    w'.site = .bar0 ∨ w'.site = .ld0 ∨ w'.P.baseWord = b32 0 := by
  by_cases h0 : w.site = .bar0
  · obtain ⟨site, P⟩ := w
    simp only at h0
    subst h0
    simp only [Worker.next, Option.some.injEq] at h
    subst h
    exact .inr (.inl rfl)
  by_cases h1 : w.site = .ld0
  · obtain ⟨site, P⟩ := w
    simp only at h1
    subst h1
    obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
    obtain ⟨t, hgd, hfire⟩ := hF
    obtain ⟨pc, ac, bs, rfl, hl, hsz⟩ := worker_ld0_shape hpre (g := g) (w := ⟨.ld0, P⟩) rfl
      ⟨t, ⟨hgd.1, hgd.2.2⟩, hfire⟩
    have hbs := hb he hl hsz
    simp only [Worker.next] at h
    simp only [hbs, rebuild_b32, Option.some.injEq] at h
    subst h
    right; right
    simp [Worker.setTm, Loader.Pro.baseWord]
  have hP : w.P.baseWord = b32 0 := hi.resolve_left h0 |>.resolve_left h1
  have hP' := worker_next_P h h1 hs
  right; right
  rw [hP', hP]

/-- **The dispatch** enters a role with the zero word in `%r2`, and the MMA warp with base 0. -/
theorem words_dispatch {g : Nat} {e : Event} {P : Loader.Pro} {a : WComp.WSt}
    (hP : P.baseWord = b32 0) (h : WComp.dispatch L g P e = some (some a)) :
    WordsInv Q L g (.w a) := by
  unfold WComp.dispatch at h
  split at h
  · rename_i d' hd
    rcases (EvW.ldRole_next hd).2 with hs | hs | hs | hs | hs <;> rw [hs] at h <;>
      simp only [WComp.roleStart] at h
    · simp only [Option.some.injEq] at h
      subst h
      show (Worker.handoff L g P).baseWord = _
      rw [Worker.handoff_baseWord, hP]
    · split at h
      · rename_i tm htm
        split_ifs at h
        · simp only [Option.some.injEq] at h
          subst h
          have h0 : tm = 0 := by
            change WComp.tmOf P.baseWord = some tm at htm
            rw [hP] at htm
            have h00 : WComp.tmOf (b32 0) = some 0 := by decide
            exact (Option.some.inj (htm.symm.trans h00))
          refine ⟨?_, h0, fun h => absurd rfl h⟩
          show (Worker.handoff L g P).baseWord = _
          rw [Worker.handoff_baseWord, hP]
        · cases h
      · cases h
    · simp only [Option.some.injEq] at h
      subst h
      exact hP
    · simp only [Option.some.injEq] at h
      subst h
      exact hP
    · simp only [Option.some.injEq] at h
      subst h
      exact Or.inr (Or.inr hP)
  · cases h
  · cases h

theorem mma_next_setMaxReg {d d' : Mma.D} {e : Event} (h : Mma.next L g d e = some (some d'))
    (hs : d.site = .setMaxReg) : d'.site = .ldNum := by
  unfold Mma.next at h
  rw [hs] at h
  simp only [Option.some.injEq] at h
  subst h
  rfl

/-- **The MMA machine's step keeps the invariant.** -/
theorem words_mma (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hn : NumWordRead Q L X) {g k : Nat} {e : Event}
    {d d' : Mma.D} {P : Loader.Pro} (he : X.get (g, k) = some e) (hg : g < L.threads)
    (hσ : St Q L X g k = some (some (.w (.mma d P))))
    (hi : P.baseWord = b32 0 ∧ d.tm = 0 ∧ (d.site ≠ .setMaxReg → d.site ≠ .ldNum →
      d.n = Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) ∧
      Mma.numWord d = b32 (Q.numIters (ProA.cta L g .z) (ProA.cta L g .x))))
    (h : Mma.next L g d e = some (some d')) :
    d'.tm = 0 ∧ (d'.site ≠ .setMaxReg → d'.site ≠ .ldNum →
      d'.n = Q.numIters (ProA.cta L g .z) (ProA.cta L g .x) ∧
      Mma.numWord d' = b32 (Q.numIters (ProA.cta L g .z) (ProA.cta L g .x))) := by
  obtain ⟨-, htm, hnn⟩ := hi
  have h1 := (WComp.mma_next_pro h).2
  refine ⟨h1.trans htm, ?_⟩
  by_cases hl : d.site = .ldNum
  · -- the read of `num_iters`
    obtain ⟨u, hF⟩ := fired_cont hX hf hg he hσ (by simp [ExitState])
    obtain ⟨t, hgd, hfire⟩ := hF
    have hsh := EvW.mma_shape hpre hg (d := d) (P := P) ⟨t, ⟨hgd.1, hgd.2.2⟩, hfire⟩
    unfold EvW.MmShape at hsh
    rw [hl] at hsh
    obtain ⟨ac, bs, rfl, hloc, hsz⟩ := hsh
    have hbs := hn he hσ hl hloc hsz
    unfold Mma.next at h
    rw [hl] at h
    simp only [hbs, rebuild_b32] at h
    have hN := numIters_lt hpre hg
    simp only [Option.some.injEq] at h
    subst h
    intro _ _
    simp only [Raw.word32Of_b32, Option.getD_some, Mma.numWord, Function.update_self, and_true]
    exact Nat.mod_eq_of_lt hN
  · intro h2 h3
    by_cases hs : d.site = .setMaxReg
    · exact absurd (mma_next_setMaxReg h hs) h3
    · rw [(mma_next_n h hl).1, Mma.numWord, (mma_next_n h hl).2]
      exact hnn hs hl

theorem idle_next_P {d d' : Worker.Idle.D} {e : Event}
    (h : Worker.Idle.next d e = some (some d')) : d'.P = d.P := by
  obtain ⟨s, P⟩ := d
  cases s <;> simp only [Worker.Idle.next, Option.some.injEq] at h <;>
    first | (subst h; rfl) | cases h

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X) (hf : ThreadFacts Q L mem0 X)
    (hb : BaseWordRead L X) (hn : NumWordRead Q L X)
include hpre hX hf hb hn

/-- **A composed worker step keeps the invariant.** -/
theorem words_wstep {g k : Nat} {e : Event} {s0 a : WComp.WSt} (he : X.get (g, k) = some e)
    (hg : g < L.threads) (hσ : St Q L X g k = some (some (.w s0))) (hi : WordsInv Q L g (.w s0))
    (h : WComp.next L g s0 e = some (some a)) : WordsInv Q L g (.w a) := by
  cases s0 with
  | worker w =>
    by_cases hs : w.site = .ldRole
    · obtain ⟨s, P⟩ := w
      simp only at hs
      subst hs
      have hP : P.baseWord = b32 0 := by
        rcases hi with h | h | h
        · cases h
        · cases h
        · exact h
      exact words_dispatch hP h
    · rw [EvW.next_worker_map hs] at h
      obtain ⟨w', hw, rfl⟩ := EvW.map_map_some h
      exact words_worker hpre hX hf hb he hg hs hσ hi hw
  | idle d =>
    by_cases hs : d.site = .inc
    · obtain ⟨s, P⟩ := d
      simp only at hs
      subst hs
      have h' : some (some (WComp.WSt.worker ⟨.loop, Worker.bumpPro P⟩)) = some (some a) := h
      simp only [Option.some.injEq] at h'
      subst h'
      exact .inr (.inr hi)
    · rw [EvW.next_idle_map hs] at h
      obtain ⟨d', hd, rfl⟩ := EvW.map_map_some h
      show d'.P.baseWord = _
      rw [idle_next_P hd]
      exact hi
  | loader d P =>
    by_cases hs : d.site = .setMaxInc
    · obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
      simp only at hs
      subst hs
      have h' : some (some (WComp.WSt.worker ⟨.loop, Worker.bumpPro P⟩)) = some (some a) := h
      simp only [Option.some.injEq] at h'
      subst h'
      exact .inr (.inr hi)
    · rw [EvW.next_loader_map P hs] at h
      obtain ⟨d', hd, rfl⟩ := EvW.map_map_some h
      exact hi
  | mma d P =>
    by_cases hs : d.site = .setMaxRegInc
    · obtain ⟨s, i, n, tm, pro⟩ := d
      simp only at hs
      subst hs
      have h' : some (some (WComp.WSt.worker ⟨.loop, Worker.bumpPro P⟩)) = some (some a) := h
      simp only [Option.some.injEq] at h'
      subst h'
      exact .inr (.inr hi.1)
    · rw [EvW.next_mma_map P hs] at h
      obtain ⟨d', hd, rfl⟩ := EvW.map_map_some h
      exact ⟨hi.1, words_mma hpre hX hf hn he hg hσ hi hd⟩
  | exit x =>
    obtain ⟨s, P⟩ := x
    cases s
    · have h' : some (some (WComp.WSt.exit ⟨.ret, P⟩)) = some (some a) := h
      simp only [Option.some.injEq] at h'
      subst h'
      exact hi
    · cases h

/-- **Every state of a thread keeps the invariant.** -/
theorem words_inv {g : Nat} :
    ∀ (k : Nat) (s : TSt), St Q L X g k = some (some s) → WordsInv Q L g s := by
  refine stateAt_induction (WordsInv Q L g) ?_ ?_
  · show WordsInv Q L g (if g % L.block < 128 then .d (DComp.code L g Q).init
      else .w (WComp.code L g Q).init)
    split
    · trivial
    · exact .inl rfl
  · intro k e s s' he' hσ hi hnx
    have he : X.get (g, k) = some e := he'
    have hg : g < L.threads := Frame.lt_of_get hX he
    cases s with
    | d s0 =>
      rw [next_d] at hnx
      obtain ⟨a, -, h⟩ := map_map_eq_some_some hnx
      subst h
      trivial
    | w s0 =>
      rw [next_w] at hnx
      obtain ⟨a, ha, h⟩ := map_map_eq_some_some hnx
      subst h
      exact words_wstep hpre hX hf hb hn he hg hσ hi ha

/-! ### `MmaWords` -/

open PTX.Kernels.InklingRelDecode.Proof.Result.Mma (AtMma reqOf splitOf)

/-- **`MmaWords.tm`.** Every MMA state has Tensor Memory base 0, from the premise on the base
word's read. -/
theorem mma_tm {m : EvId} {d : Mma.D} (h : AtMma Q L X m d) : d.tm = 0 := by
  obtain ⟨P, hσ⟩ := h
  exact (words_inv hpre hX hf hb hn m.2 _ hσ).2.1

/-- **`MmaWords.iters`, past the read.** The loop bound of an MMA state past the read of
`num_iters` (every site but `setMaxReg` and `ldNum`) is the split's `num_iters`, from the premise
on that word's read. -/
theorem mma_iters {m : EvId} {d : Mma.D} (h : AtMma Q L X m d) (hs : d.site ≠ .setMaxReg)
    (hl : d.site ≠ .ldNum) : d.n = Q.numIters (reqOf L m.1) (splitOf L m.1) := by
  obtain ⟨P, hσ⟩ := h
  exact ((words_inv hpre hX hf hb hn m.2 _ hσ).2.2 hs hl).1

/-- **`MmaWords.iters` at the QK and PV sites** (the only places the data path uses it). -/
theorem mma_iters_loop {m : EvId} {d : Mma.D} (h : AtMma Q L X m d)
    (hs : Mma.QkSite d.site ∨ Mma.PvSite d.site) :
    d.n = Q.numIters (reqOf L m.1) (splitOf L m.1) := by
  refine mma_iters hpre hX hf hb hn h ?_ ?_
  · rcases hs with hs | hs <;> intro h0 <;> rw [h0] at hs <;> exact hs
  · rcases hs with hs | hs <;> intro h0 <;> rw [h0] at hs <;> exact hs

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
