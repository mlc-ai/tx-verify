-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.KvCov
public import Kernels.InklingRelDecode.Proof.Thread.ProAPsh
public import Kernels.InklingRelDecode.Proof.Thread.Lk5VPro
public import Kernels.InklingRelDecode.Proof.Thread.Lk5VSm

@[expose] public section

/-! # The prologue's broadcasts receive the warp index

Each preloaded block `b` of the prologue broadcasts the warp index (`shfl.sync.idx` from lane 0,
`psh b`) and its four copies fill the half of the slot that bit 0 of the received word names
(`Proof.ProA.half`). By DEP-WARP-SHFL the word is lane 0's operand at the same instance, or any
value when lane 0 exited before it (`Frame.shfl_src`).

* **The count** (`PSH`, `psh_inv`): along a thread of warps 0 to 3 the shuffles are one after the
  startup, `1 + proW` at a prologue state (`Proof.ProA.proW`: the broadcasts passed, `num_pre`
  after the blocks), at least `1 + num_pre` in the softmax region and the epilogue.
* **The source** (`psh_recv`): a broadcast of block `b` has `1 + b` shuffles before it and
  `b < num_pre`; lane 0's exit has at least `1 + num_pre` (`dp_exit_cnt`), and its shuffle with
  `1 + b` before it is the startup's or a broadcast, which send the warp index.
* **The word along the prologue** (`PSO`, `pso_inv`): after the broadcast of block `b` the
  recorded word is the warp index; and every copy the thread made is at an earlier position than
  its state's, so a copy site fires once (`pro_copy_once`).

`pro_half`: a prologue copy of block `b` fills the half `warp % 2`. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### The prologue's shuffle sites -/

theorem pro_shflS (s : ProA.Site) (h : s.pc ∈ shflPcs) : ∃ b, s = .psh b := by
  cases s with
  | psh b => exact ⟨b, rfl⟩
  | ld k | el k | init k | arr k | ldq k | st9 k => revert h; fin_cases k <;> decide
  | pb b j | lb b j | pel b j | ptc b j | stq b j =>
    revert h; fin_cases b <;> fin_cases j <;> decide
  | _ => revert h; decide

theorem psh_old (b : Fin 3) : Proof.ProA.proShfl (ProA.Site.psh b).old = true := by
  fin_cases b <;> rfl

theorem pro_proShfl_iff (s : ProA.Site) :
    Proof.ProA.proShfl s.old = true ↔ ∃ b, s = .psh b := by
  constructor
  · intro h
    cases s with
    | psh b => exact ⟨b, rfl⟩
    | ld k | el k | init k | arr k | ldq k | st9 k => revert h; fin_cases k <;> decide
    | pb b j | lb b j | pel b j | ptc b j | stq b j =>
      revert h; fin_cases b <;> fin_cases j <;> decide
    | _ => revert h; decide
  · rintro ⟨b, rfl⟩; exact psh_old b

/-- **A prologue step adds one broadcast exactly at a broadcast site**, unless it enters the
exit. -/
theorem pro_proW {d d' : ProA.D} {e : Event} (h : ProA.next L g d e = some (some d'))
    (hx : d'.site ≠ .exit) (hG : Proof.ProA.Gate L g d.site.old d.dt) :
    Proof.ProA.proW L g d'.old =
      Proof.ProA.proW L g d.old + if Proof.ProA.proShfl d.site.old then 1 else 0 := by
  obtain ⟨s, dt⟩ := d
  by_cases hk : ProA.kill ⟨s, dt⟩ e = true
  · simp [ProA.next, hk] at h
  have h' : ProA.next0 L g ⟨s, dt⟩ e = some (some d') := by simpa [ProA.next, hk] using h
  by_cases h1 : s = .bar18
  · subst h1
    exact absurd (by simp [ProA.next0] at h'; rw [← h']) hx
  by_cases h2 : s = .exit
  · subst h2; simp [ProA.next0] at h'
  by_cases h3 : s = .ld 2
  · subst h3
    have hs := ld2_succ h'
    obtain ⟨s', dt'⟩ := d'
    simp only at hs
    subst hs
    simp only [ProA.D.old]
    rw [Proof.ProA.proW_lit _ (by decide), Proof.ProA.proW_lit _ (by decide)]
    rfl
  have hf := ProA.next0_flat h1 h2 h3 h'
  have hf' : Proof.ProA.next L g ⟨s.old, dt⟩ e = some (some (ProA.D.old d')) := hf
  exact Proof.ProA.proW_next hf' hG

/-! ### The count of shuffles along a thread of warps 0 to 3 -/

/-- The softmax region's iterations: `num_iters` as `%r26` holds it. -/
def smIt (Q : Params) (L : Launch) (g : Nat) : Nat :=
  if Q.numIters (Proof.ProA.cta L g .z) (Proof.ProA.cta L g .x) < 2 ^ 31 then
    Q.numIters (Proof.ProA.cta L g .z) (Proof.ProA.cta L g .x) else 0

/-- **The shuffles of a thread of warps 0 to 3**: `1 + proW` at a prologue state,
`1 + num_pre + smW` in the softmax region, and in the epilogue at least the softmax region's
`1 + num_pre + smBase` of its iterations. -/
def PSH (Q : Params) (L : Launch) (g : Nat) : (thread Q L g).D → Nat → Prop
  | (.inr ⟨.inl (.dp _ _), .inl d⟩, _), s => s = 1 + Proof.ProA.proW L g d.old
  | (.inr ⟨.inl (.dp _ _), .inr ⟨.inl _, .sm d⟩⟩, _), s =>
    s = 1 + npOf Q L g + Proof.Sm.smW d ∧ (Proof.Sm.smMid d.site = true → 1 ≤ d.i)
  | (.inr ⟨.inl (.dp _ _), .inr ⟨.inl _, .epi _⟩⟩, _), s =>
    1 + npOf Q L g + Proof.Sm.smBase (smIt Q L g) ≤ s
  | _, _ => True

/-- The softmax region's shuffle sites. -/
theorem sm_shflS (s : Proof.Sm.Site) (h : s.pc ∈ shflPcs) : Proof.Sm.smShfl s = true := by
  revert h
  cases s <;> (try (rename_i j; revert j)) <;> decide +kernel

/-- A softmax step at a shuffle site is fired by a shuffle. -/
theorem sm_next_shfl {d d' : Proof.Sm.D} {e : Event} (h : Proof.Sm.next L g d e = some (some d'))
    (hs : Proof.Sm.smShfl d.site = true) : Execution.isShfl e = true := by
  obtain ⟨pc, k⟩ := e
  rcases Proof.Sm.smShfl_cases hs with hs | hs | hs | hs | hs | hs | hs | hs | hs <;>
    simp only [Proof.Sm.next, hs] at h <;> (cases k <;> simp_all [Execution.isShfl])

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
/-- The count of a softmax state at an event that leaves the loop (as the first tree's
`Lk.leaves_smW`). -/
theorem leaves_smW' {d : Proof.Sm.D} {e : Event} (hl : Proof.DComp.leaves L g d e) :
    Proof.Sm.smW d = Proof.Sm.smBase d.e.r26 ∧ Proof.Sm.smShfl d.site = false := by
  obtain ⟨s, en, i, m, l, cw, cv, w, v, sv, pf, stg⟩ := d
  cases s <;> simp only [Proof.DComp.leaves] at hl <;>
    first
    | exact absurd hl id
    | (simp only [Proof.Sm.smW, Proof.Sm.smOff, Proof.Sm.smShfl, hl.2, and_true]; simp)
    | (simp only [Proof.Sm.smW, Proof.Sm.smOff, Proof.Sm.smShfl, hl.2.2, and_true]; simp)
    | (simp only [Proof.Sm.smW, Proof.Sm.smOff, Proof.Sm.smShfl, and_true]
       rw [hl.2, Proof.Sm.smBase_succ])

/-- `%r26` of a softmax state is the CTA's iterations. -/
theorem r26_smIt {d : Proof.Sm.D} (hI : Proof.Sm.Inv L g d) (hR : SmRef Q L g d) :
    d.e.r26 = smIt Q L g := by
  rw [hI.ok.r26, hR.r25]
  rfl

/-- **A tail state's count is at least `1 + num_pre`.** -/
theorem tail_cnt {tm : Nat} {bw : Value} {dt : Proof.ProA.Dat} {τ : Tail.St} {n : Cls → Nat}
    {c : Nat} (h : PSH Q L g (.inr ⟨.inl (.dp tm bw), .inr ⟨.inl dt, τ⟩⟩, n) c) :
    1 + npOf Q L g ≤ c := by
  cases τ with
  | sm d => have : _ ∧ _ := h; omega
  | epi d => have : 1 + npOf Q L g + _ ≤ c := h; omega

theorem countP_snoc2 (P : Event → Bool) (l : List Event) (e : Event) :
    (l ++ [e]).countP P = l.countP P + if P e then 1 else 0 := by
  simp only [List.countP_append, List.countP_singleton]

/-- `num_pre` from the prologue's guards, at a site whose request words are loaded. -/
theorem npOf_flat (hp : Pre Q L m) (hg : g < L.threads) {tm : Nat} {bw : Value} {d : ProA.D}
    (hR : ProA.PRef Q L g tm bw d) (ha : Proof.ProA.ArgsOk L g d.dt.pro)
    (hk : d.site.old.afterSk = true) (h1 : d.site.old ≠ .sMax) (h2 : d.site.old ≠ .ldCu0) :
    Proof.ProA.npOf L g d.dt = npOf Q L g := by
  have hspl := hp.splitsRange
  have hw : d.dt.pro.w71 = Q.splits := by
    rw [hR.pro]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨w0, w1, w2⟩ := hR.words
  have hm : Proof.ProA.WordsMatch Q (Proof.ProA.cta L g .z) d.dt :=
    ⟨w0 h1 h2, w1 (.inl hk), w2 hk⟩
  exact Proof.ProA.npOf_eq hp hg ha hw hm

set_option maxHeartbeats 1000000 in
/-- **The shuffles of a thread of warps 0 to 3 along it.** -/
theorem psh_inv (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) :
    ∀ k, k < (X.tr g).length → ∀ σ, Frame.stateAt (thread Q L) X g k = some (some σ) →
      PSH Q L g σ (((X.tr g).take k).countP Execution.isShfl) := by
  intro k
  induction k with
  | zero =>
    intro _ σ hσ
    rw [Frame.stateAt_zero, thread_init_eq] at hσ
    obtain rfl := Option.some.inj (Option.some.inj hσ)
    trivial
  | succ k ih =>
    intro hk σ' hσ'
    have hlt : k < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    rw [Frame.stateAt_succ he] at hσ'
    have hF := good_all' hp hX hg k
    have htake : (X.tr g).take (k + 1) = (X.tr g).take k ++ [e] := by
      rw [List.take_add_one, he, Option.toList_some]
    rw [htake, countP_snoc2]
    rcases hk0 : Frame.stateAt (thread Q L) X g k with _ | _ | σ
    · rw [hk0] at hσ'; cases hσ'
    · exact absurd hk0 hF.1
    · rw [hk0] at hσ'
      have hn : (thread Q L g).next σ e = some (some σ') := hσ'
      have hJ := hF.2 σ hk0
      have hR0 := ih hlt σ hk0
      obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
        Frame.fired_site (fun g hg => thread_sound hp hg) hX he hk0
      have hnE : ¬ Ends e := not_ends_of_lt hX hg he hk
      have hsh : ∀ hs : Execution.isShfl e = true, (thread Q L g).pc σ ∈ shflPcs :=
        fun hs => shfl_pc hc hf hs
      cases o with
      | none => exact absurd (fires_none_ends hf) hnE
      | some u =>
      obtain ⟨x, n⟩ := σ
      rcases x with st | ⟨_ | r, d⟩
      · -- the startup enters the prologue after its shuffle
        rw [next_start] at hn
        obtain ⟨s', hs', rfl⟩ := mm_some hn
        simp only [Code.enter]
        split
        · rename_i j hj
          rcases j with (_ | _) | _
          · have hx : ∃ r, Startup.enterOf s' = some r := by
              simp only [Code.gatedExit] at hj
              cases hq : Startup.enterOf s' with
              | none => rw [hq] at hj; simp at hj
              | some r => exact ⟨r, rfl⟩
            obtain ⟨r, hr⟩ := hx
            have hsr : s'.site = .enter r := by
              simp only [Startup.enterOf] at hr
              split at hr <;> simp_all
            have hshs := succ_enter hs' hsr
            have hev : Startup.Ev L g st e := frag_ev hp hg hJ hat hi hc hf
            obtain ⟨site, tm0, x0, w0⟩ := st
            simp only at hshs
            subst hshs
            simp only [Startup.Ev] at hev
            obtain ⟨recv, ok, rfl⟩ := hev
            have hS : StartRef ⟨.shfl, tm0, x0, w0⟩ n := hJ
            have hn0 : n .shfl = 0 := hS.1
            have hfc := fcount hk0 .shfl
            simp only [cls] at hfc
            have hn0' : ((X.tr g).take k).countP Execution.isShfl = 0 := by
              rw [← hfc]; exact hn0
            show _ = 1 + Proof.ProA.proW L g (ProA.init _ _).old
            rw [Proof.ProA.proW_lit _ rfl, hn0']
            rfl
          · trivial
          · trivial
        · trivial
      · rename_i i
        obtain ⟨d', hd'⟩ := next_same_role hn
        obtain ⟨x', n'⟩ := σ'
        simp only at hd'
        subst hd'
        cases i with
        | worker w => trivial
        | dp tm bw =>
          rcases d with d | ⟨_ | _, τ⟩
          · rw [next_pro] at hn
            obtain ⟨d'', hd'', he''⟩ := mm_some hn
            have hR : ProRef Q L g tm bw d n := hJ
            have hR0' : _ = 1 + Proof.ProA.proW L g d.old := hR0
            have hxd : d.site ≠ .exit := proA_site_ne (Code.gatedExit_none.mp hi.2)
            -- the event is a shuffle exactly at a broadcast site
            have hsi : (if Execution.isShfl e then 1 else 0) =
                if Proof.ProA.proShfl d.site.old then 1 else 0 := by
              cases hq : Execution.isShfl e
              · cases hp' : Proof.ProA.proShfl d.site.old
                · rfl
                · exfalso
                  obtain ⟨b, hb⟩ := (pro_proShfl_iff _).mp hp'
                  have hev := ProA.shape (L := L) (g := g) (Startup.inh L g Q tm) hxd hat hi.1 hc hf
                  simp only [ProA.Ev, hb] at hev
                  obtain ⟨recv, ok, rfl⟩ := hev
                  simp [Execution.isShfl] at hq
              · obtain ⟨b, hb⟩ := pro_shflS d.site (hsh hq)
                rw [(pro_proShfl_iff _).mpr ⟨b, hb⟩]
            have hx : ProA.exitOf d'' = none ∨ ∃ v, ProA.exitOf d'' = some v := by
              cases ProA.exitOf d'' <;> simp
            rcases hx with hx | ⟨v, hxo⟩
            · rw [Code.enter_none (by simp [Code.gatedExit, hx])] at he''
              simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq, true_and] at he''
              obtain ⟨rfl, -⟩ := he''
              show _ = 1 + Proof.ProA.proW L g d''.old
              have hx'' : d''.site ≠ .exit := proA_site_ne hx
              rw [pro_proW hd'' hx'' hR.2.2.1.gate, hR0', hsi]
              omega
            · -- the prologue's exit enters the softmax region or its stub
              have hxs : d''.site = .exit := by
                simp only [ProA.exitOf] at hxo; split at hxo <;> simp_all
              have hb18 := exit_from_bar18 hd'' hxs
              have hnp : Proof.ProA.npOf L g d.dt = npOf Q L g :=
                npOf_flat hp hg hR.2.2.1 hi.1.args (by rw [hb18]; rfl) (by rw [hb18]; decide)
                  (by rw [hb18]; decide)
              have hpw : Proof.ProA.proW L g d.old = npOf Q L g := by
                rw [← hnp]
                obtain ⟨s, dt⟩ := d
                simp only at hb18
                subst hb18
                exact Proof.ProA.proW_q _ rfl
              cases hsel : ProA.selTail Q L g v d'' with
              | some dt' =>
                rw [Code.enter_some (i := Sum.inl dt')
                  (by simp [Code.gatedExit, hxo, hsel])] at he''
                simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq,
                  true_and] at he''
                obtain ⟨rfl, -⟩ := he''
                refine ⟨?_, fun h => by simp [tailInit, Proof.SmEntry.d0, Proof.Sm.smMid] at h⟩
                simp only [tailInit, Proof.SmEntry.d0, Proof.Sm.smW, Proof.Sm.smBase,
                  Proof.Sm.smOff, ite_true]
                have : Execution.isShfl e = false := by
                  cases hq : Execution.isShfl e
                  · rfl
                  · obtain ⟨b, hb⟩ := pro_shflS d.site (hsh hq)
                    rw [hb18] at hb; cases hb
                simp only [this, Bool.false_eq_true, ite_false]
                omega
              | none =>
                rw [Code.enter_some (i := Sum.inr ())
                  (by simp [Code.gatedExit, hxo, hsel])] at he''
                simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq,
                  true_and] at he''
                obtain ⟨rfl, -⟩ := he''
                trivial
          · rw [next_tail] at hn
            obtain ⟨τ', hτ, he''⟩ := mm_some hn
            simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq, true_and] at he''
            obtain ⟨rfl, -⟩ := he''
            have hge := tail_cnt hR0
            cases τ with
            | epi d =>
              simp only [Tail.next] at hτ
              obtain ⟨d', -, rfl⟩ := mm_some hτ
              have : 1 + npOf Q L g + _ ≤ _ := hR0
              show 1 + npOf Q L g + _ ≤ _
              omega
            | sm d =>
              obtain ⟨hc, hm⟩ : _ ∧ _ := hR0
              simp only [Tail.next] at hτ
              split at hτ
              · rename_i hl
                have hw := (leaves_smW' hl).1
                have hI : Proof.Sm.Inv L g d := hi
                obtain ⟨-, -, hSR⟩ := (hJ : TailRef Q L g tm (.sm d) n)
                rw [r26_smIt hI hSR] at hw
                simp only [Tail.exitNext] at hτ
                split at hτ
                · simp only [Option.some.injEq] at hτ
                  subst hτ
                  show 1 + npOf Q L g + _ ≤ _
                  omega
                · cases hτ
              · obtain ⟨d', hd', rfl⟩ := mm_some hτ
                obtain ⟨hw, hm'⟩ := Proof.Sm.smW_next hd' hm
                refine ⟨?_, hm'⟩
                have hsi : (if Execution.isShfl e then 1 else 0) =
                    if Proof.Sm.smShfl d.site then 1 else 0 := by
                  cases hq : Execution.isShfl e
                  · cases hp' : Proof.Sm.smShfl d.site
                    · rfl
                    · rw [sm_next_shfl hd' hp'] at hq; cases hq
                  · rw [sm_shflS d.site (hsh hq)]
                rw [hc, hw, hsi]
                omega
          · exact hJ.elim
      · exact hJ.elim

/-! ### The broadcast's source -/

/-- **A thread of warps 0 to 3 exits after at least `1 + num_pre` shuffles.** -/
theorem dp_exit_cnt (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {h j pc : Nat} (hE : X.get (h, j) = some ⟨pc, .exit⟩) (hw : h % L.block < 128) :
    1 + npOf Q L h ≤ ((X.tr h).take j).countP Execution.isShfl := by
  have hb : L.block = 256 := hp.block
  have hh := Frame.lt_of_get hX hE
  have hlen : j < (X.tr h).length := (List.getElem?_eq_some_iff.mp hE).1
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX hE (fun f h => by cases h)
  have hpc := ret_pc' hc hf rfl
  obtain ⟨x, n⟩ := σ
  rcases x with st | ⟨_ | r, d⟩
  · exfalso
    have hm := startup_special st.site (List.mem_append_right _ hpc)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h' | h' | h' <;>
      rw [show (thread Q L h).pc _ = st.site.pc from rfl, h'] at hpc <;>
      simp [retPcs, Startup.Site.pc] at hpc
  · rename_i i
    cases i with
    | dp tm bw =>
      rcases d with d | ⟨_ | _, τ⟩
      · exact absurd (List.mem_append_right _ hpc) (proA_special d.site)
      · exact tail_cnt (psh_inv hp hX hh j hlen _ hσ)
      · exact hJ.elim
    | worker w =>
      have : 4 ≤ h % L.block / 32 := (tm_inv hp hX hh j hlen _ hσ).2
      omega
  · exact hJ.elim

theorem pshB_psh (b : Fin 3) : Proof.ProA.pshB (ProA.Site.psh b).old = b.val := by
  fin_cases b <;> rfl

theorem npOf_cta' {h : Nat} (hc : h / L.block = g / L.block) : npOf Q L h = npOf Q L g := by
  simp only [npOf, Proof.ProA.cta, hc]

/-- **Every broadcast of the prologue receives the warp index**: the source, lane 0 of the warp,
made the shuffle of the same instance (its exit has at least `1 + num_pre` shuffles before it,
the broadcast of block `b` has `1 + b` with `b < num_pre`), and every shuffle of a thread of
warps 0 to 3 with fewer than `1 + num_pre` before it is the startup's or a broadcast, both of
which send the warp index. -/
theorem psh_recv (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k pc : Nat} {mode : ShflMode} {a recv : Value} {b c : Nat} {ok : Bool}
    (he : X.get (g, k) = some ⟨pc, .shfl mode a b c recv ok⟩) {tm : Nat} {bw : Value}
    {d : ProA.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread Q L) X g k =
      some (some (.inr ⟨.inl (.dp tm bw), .inl d⟩, n))) :
    recv = b32 (g % L.block / 32) := by
  have hb : L.block = 256 := hp.block
  have hb32 : L.block % 32 = 0 := by rw [hb]
  have hg := Frame.lt_of_get hX he
  have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  have hdp : g % L.block < 128 := dp_lane k hσ
  obtain ⟨σ, t, ins, o, hσ', hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
  rw [hσ] at hσ'
  obtain rfl := Option.some.inj (Option.some.inj hσ')
  cases o with
  | none => exact absurd (fires_none_ends hf) (by simp [Ends])
  | some u =>
  have hR : ProRef Q L g tm bw d n := hJ
  have hxd : d.site ≠ .exit := proA_site_ne (Code.gatedExit_none.mp hi.2)
  obtain ⟨bk, hbk⟩ := pro_shflS d.site (shfl_pc hc hf (by simp [Execution.isShfl]))
  have hev := ProA.shape (L := L) (g := g) (Startup.inh L g Q tm) hxd hat hi.1 hc hf
  simp only [ProA.Ev, hbk] at hev
  obtain ⟨recv', ok', heq⟩ := hev
  simp only [Event.mk.injEq, Kind.shfl.injEq] at heq
  obtain ⟨-, rfl, -, rfl, rfl, -, -⟩ := heq
  -- the broadcast's count
  have hS : _ = 1 + Proof.ProA.proW L g d.old := psh_inv hp hX hg k hlen _ hσ
  have hpw : Proof.ProA.proW L g d.old = bk.val := by
    obtain ⟨s, dt⟩ := d
    simp only at hbk
    subst hbk
    rw [Proof.ProA.proW_lit _ (by fin_cases bk <;> rfl)]
    exact pshB_psh bk
  have hG := hR.2.2.1.gate
  have hblk := Proof.ProA.lt_npOf hG (Proof.ProA.psh_blk _ (by rw [hbk]; exact psh_old bk))
  have hnp : Proof.ProA.npOf L g d.dt = npOf Q L g :=
    npOf_flat hp hg hR.2.2.1 hi.1.args (by rw [hbk]; fin_cases bk <;> rfl)
      (by rw [hbk]; fin_cases bk <;> decide) (by rw [hbk]; fin_cases bk <;> decide)
  rw [hbk, pshB_psh, hnp] at hblk
  have hcv : ((X.tr g).take k).countP (voteWith (2 ^ 32 - 1)) = 0 :=
    List.countP_eq_zero.mpr fun e he' => by
      obtain ⟨i, hi'⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take he')
      simp [novote hX (i := (g, i)) hi']
  have IH : Frame.GoodUpTo (thread Q L) (fun g => Ref Q L g) X (g % L.block / 32)
      (((X.tr g).take k).countP Execution.isShfl + 0) :=
    fun h j hh _ => good_all' hp hX hh.1 j
  obtain ⟨j, pc', b', c', r', o', hget, hG', hcs, -⟩ := Frame.shfl_src (C := thread Q L)
    (J := fun g => Ref Q L g) hb32 hX hg rfl he rfl IH
    (fun _ _ _ _ _ he' hv _ _ _ => by rw [novote hX he'] at hv; cases hv)
    (fun h j' pcx hh hcta hx _ hs _ => by
      have hw : h % L.block < 128 := by
        have := hh.2; have := Nat.mod_lt h (show 0 < L.block by omega); omega
      have hx' := dp_exit_cnt hp hX hx hw
      rw [npOf_cta' hcta] at hx'
      unfold Frame.cnt at hs
      omega)
  -- the source's shuffle sends the warp index
  have hsl := Step.shflSource_lt ShflMode.idx
    (show laneOf L g < 32 from Nat.mod_lt _ (by decide)) 0 31
  obtain ⟨hsT, hsW, hsC, -, -⟩ := Frame.lane_facts hb32 hg rfl hsl
  set src := g - laneOf L g + (shflSource ShflMode.idx (laneOf L g) 0 31).1 with hsrc
  have hlj : j < (X.tr src).length := (List.getElem?_eq_some_iff.mp hget).1
  have hcs' : ((X.tr src).take j).countP Execution.isShfl = 1 + bk.val := by
    unfold Frame.cnt at hcs; omega
  obtain ⟨σs, ts, inss, os, hσs, hJs, hats, his, hcs'', hfs⟩ :=
    ev_state hp hX hget (fun f h => by cases h)
  cases os with
  | none => exact absurd (fires_none_ends hfs) (by simp [Ends])
  | some us =>
  have hpcs := shfl_pc hcs'' hfs (by simp [Execution.isShfl])
  obtain ⟨xs, ns'⟩ := σs
  rcases xs with st | ⟨_ | r, ds⟩
  · -- the startup's shuffle
    have hevs := frag_ev hp hsT hJs hats his hcs'' hfs
    have hs : st.site = .shfl := by
      revert hpcs
      obtain ⟨site, tm0, x0, w0⟩ := st
      cases site with
      | enter r => exact fun _ => hJs.elim
      | shfl => exact fun _ => rfl
      | _ => intro h; simp [shflPcs, Startup.Site.pc] at h
    have h' : Startup.Ev L src st _ := hevs
    simp only [Startup.Ev, hs] at h'
    obtain ⟨recv', ok', heq⟩ := h'
    simp only [Event.mk.injEq, Kind.shfl.injEq, true_and] at heq
    simp [heq.2.1, hsW]
  · rename_i i
    cases i with
    | dp tm' bw' =>
      rcases ds with ds | ⟨_ | _, τ⟩
      · have hxs : ds.site ≠ .exit := proA_site_ne (Code.gatedExit_none.mp his.2)
        obtain ⟨b2, hb2⟩ := pro_shflS ds.site hpcs
        have hev2 := ProA.shape (L := L) (g := src) (Startup.inh L src Q tm') hxs hats his.1
          hcs'' hfs
        simp only [ProA.Ev, hb2] at hev2
        obtain ⟨recv2, ok2, heq2⟩ := hev2
        simp only [Event.mk.injEq, Kind.shfl.injEq, true_and] at heq2
        simp [heq2.2.1, hsW]
      · exfalso
        have h1 := tail_cnt (psh_inv hp hX hsT j hlj _ hσs)
        rw [npOf_cta' hsC, hcs'] at h1
        omega
      · exact hJs.elim
    | worker w =>
      exfalso
      have : 4 ≤ src % L.block / 32 := (tm_inv hp hX hsT j hlj _ hσs).2
      rw [hsW] at this
      omega
  · exact hJs.elim

/-! ### The received words and the copy positions along the prologue -/

/-- An event is a tensor copy. -/
def IsCopy (e : Event) : Prop := ∃ a sp, e.kind = .tensorIssue a sp

/-- **At a prologue state**: after the broadcast of block `b` the recorded word is the warp
index, and every copy before the state was at an earlier position than the state's. -/
def PSO (Q : Params) (L : Launch) (g : Nat) : (thread Q L g).D → List Event → Prop
  | (.inr ⟨.inl (.dp _ _), .inl d⟩, _), es =>
    (∀ j < 3, d.site.old ∈ Proof.ProA.pshAfter j →
      Proof.ProA.shOf d.dt j = b32 (g % L.block / 32)) ∧
    ∀ e ∈ es, IsCopy e → e.pc < d.site.pc
  | _, _ => True

theorem pshAfter_not_psh {j : Nat} (hj : j < 3) {s : Proof.ProA.Site}
    (h : s ∈ Proof.ProA.pshAfter j) : s ∉ Proof.ProA.pshSites := by
  interval_cases j <;> revert h <;> cases s <;> decide

theorem shOf_keep {dt dt' : Proof.ProA.Dat}
    (h : dt'.sh0 = dt.sh0 ∧ dt'.sh1 = dt.sh1 ∧ dt'.sh2 = dt.sh2) (j : Nat) :
    Proof.ProA.shOf dt' j = Proof.ProA.shOf dt j := by
  match j with
  | 0 => exact h.1
  | 1 => exact h.2.1
  | j + 2 => exact h.2.2

theorem pshSite_old {j : Nat} (hj : j < 3) {s : ProA.Site} (h : s.old = Proof.ProA.pshSite j) :
    s = .psh ⟨j, hj⟩ := by
  have h' := congrArg ProA.Site.ofOld h
  rw [ProA.ofOld_old s (fun hx => by subst hx; interval_cases j <;> cases h)] at h'
  rw [h']
  interval_cases j <;> rfl

/-- **One prologue step keeps the received words** (the flat machine's step, or the step of the
third request word, which enters the first election). -/
theorem pso_words (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k : Nat} {tm : Nat} {bw : Value} {d d'' : ProA.D} {n : Cls → Nat} {e : Event}
    (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread Q L) X g k = some (some (.inr ⟨.inl (.dp tm bw), .inl d⟩, n)))
    (hI : ∀ j < 3, d.site.old ∈ Proof.ProA.pshAfter j →
      Proof.ProA.shOf d.dt j = b32 (g % L.block / 32))
    (hd : ProA.next L g d e = some (some d'')) (hx : d''.site ≠ .exit) :
    ∀ j < 3, d''.site.old ∈ Proof.ProA.pshAfter j →
      Proof.ProA.shOf d''.dt j = b32 (g % L.block / 32) := by
  obtain ⟨s, dt⟩ := d
  have hk : ProA.kill ⟨s, dt⟩ e = false := by
    cases hq : ProA.kill ⟨s, dt⟩ e
    · rfl
    · simp [ProA.next, hq] at hd
  have h' : ProA.next0 L g ⟨s, dt⟩ e = some (some d'') := by simpa [ProA.next, hk] using hd
  intro j hj hm
  by_cases h1 : s = .bar18
  · subst h1; exact absurd (by simp [ProA.next0] at h'; rw [← h']) hx
  by_cases h2 : s = .exit
  · subst h2; simp [ProA.next0] at h'
  by_cases h3 : s = .ld 2
  · subst h3
    have hs := ld2_succ h'
    rw [hs] at hm
    exfalso
    interval_cases j <;> revert hm <;> decide
  have hf := ProA.next0_flat h1 h2 h3 h'
  have hf' : Proof.ProA.next L g ⟨s.old, dt⟩ e = some (some (ProA.D.old d'')) := hf
  rcases Proof.ProA.pshAfter_next hf' j hj hm with hs | hs
  · exact (shOf_keep (Proof.ProA.sh_next hf' (pshAfter_not_psh hj hs)) j).trans (hI j hj hs)
  · rw [hs] at hf'
    obtain ⟨mo, av, b, c, recv, ok, hkd, hsh, -, -⟩ := Proof.ProA.next_psh hj hf'
    have he' : X.get (g, k) = some ⟨e.pc, .shfl mo av b c recv ok⟩ := by
      rw [he, ← hkd]
    rw [show d''.dt = (ProA.D.old d'').dt from rfl, hsh]
    exact psh_recv hp hX he' hσ

set_option maxHeartbeats 1000000 in
/-- **The received words and the copy positions along every thread.** -/
theorem pso_inv (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) :
    ∀ k, k < (X.tr g).length → ∀ σ, Frame.stateAt (thread Q L) X g k = some (some σ) →
      PSO Q L g σ ((X.tr g).take k) := by
  intro k
  induction k with
  | zero =>
    intro _ σ hσ
    rw [Frame.stateAt_zero, thread_init_eq] at hσ
    obtain rfl := Option.some.inj (Option.some.inj hσ)
    trivial
  | succ k ih =>
    intro hk σ' hσ'
    have hlt : k < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem hlt⟩
    rw [Frame.stateAt_succ he] at hσ'
    have hF := good_all' hp hX hg k
    have htake : (X.tr g).take (k + 1) = (X.tr g).take k ++ [e] := by
      rw [List.take_add_one, he, Option.toList_some]
    rw [htake]
    have hget : X.get (g, k) = some e := he
    rcases hk0 : Frame.stateAt (thread Q L) X g k with _ | _ | σ
    · rw [hk0] at hσ'; cases hσ'
    · exact absurd hk0 hF.1
    · rw [hk0] at hσ'
      have hn : (thread Q L g).next σ e = some (some σ') := hσ'
      have hJ := hF.2 σ hk0
      have hR0 := ih hlt σ hk0
      obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
        Frame.fired_site (fun g hg => thread_sound hp hg) hX he hk0
      have hnE : ¬ Ends e := not_ends_of_lt hX hg he hk
      cases o with
      | none => exact absurd (fires_none_ends hf) hnE
      | some u =>
      obtain ⟨x, n⟩ := σ
      rcases x with st | ⟨_ | r, d⟩
      · -- the startup: no copy before the prologue
        have hK : objN ((X.tr g).take k) = 0 := kc_inv hp hX hg k hlt _ hk0
        rw [next_start] at hn
        obtain ⟨s', hs', rfl⟩ := mm_some hn
        simp only [Code.enter]
        split
        · rename_i j hj
          rcases j with (_ | _) | _
          · have he0 : isObjEv e = false := by
              cases hq : isObjEv e
              · rfl
              · exact absurd (obj_pc hc hf hq) (fun h => startup_obj st.site h)
            refine ⟨fun j hj hm => ?_, fun e' he' hcp => ?_⟩
            · exfalso
              change Proof.ProA.Site.sMax ∈ Proof.ProA.pshAfter j at hm
              interval_cases j <;> revert hm <;> decide
            · exfalso
              obtain ⟨a, sp, hk'⟩ := hcp
              have hob : isObjEv e' = true := by simp [isObjEv, hk']
              have h0 : objN ((X.tr g).take k ++ [e]) = 0 := by
                rw [objN_snoc, hK, he0]; rfl
              have := List.countP_pos_iff.mpr ⟨e', he', hob⟩
              unfold objN at h0
              omega
          · trivial
          · trivial
        · trivial
      · rename_i i
        obtain ⟨d', hd'⟩ := next_same_role hn
        obtain ⟨x', n'⟩ := σ'
        simp only at hd'
        subst hd'
        cases i with
        | worker w => trivial
        | dp tm bw =>
          rcases d with d | ⟨_ | _, τ⟩
          · rw [next_pro] at hn
            obtain ⟨d'', hd'', he''⟩ := mm_some hn
            have hR : ProRef Q L g tm bw d n := hJ
            obtain ⟨hW0, hC0⟩ : _ ∧ _ := hR0
            have hxd : d.site ≠ .exit := proA_site_ne (Code.gatedExit_none.mp hi.2)
            have hx : ProA.exitOf d'' = none ∨ ∃ v, ProA.exitOf d'' = some v := by
              cases ProA.exitOf d'' <;> simp
            rcases hx with hx | ⟨v, hxo⟩
            · rw [Code.enter_none (by simp [Code.gatedExit, hx])] at he''
              simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq, true_and] at he''
              obtain ⟨rfl, -⟩ := he''
              have hx'' : d''.site ≠ .exit := proA_site_ne hx
              refine ⟨pso_words hp hX hget hk0 hW0 hd'' hx'', fun e' he' hcp => ?_⟩
              obtain ⟨hle, hlt'⟩ := pro_pc_le hd''
              rcases List.mem_append.mp he' with he' | he'
              · exact lt_of_lt_of_le (hC0 e' he' hcp) hle
              · rw [List.mem_singleton.mp he'] at hcp ⊢
                obtain ⟨a, sp, hk'⟩ := hcp
                rcases pro_ev_kv hp hR hat hi.1 hxd hc hf with
                  ⟨b0, hs, hk''⟩ | ⟨b0, j, hs, -⟩ | ⟨-, hnc⟩
                · rw [hk'] at hk''; cases hk''
                · have hpc : e.pc = d.site.pc := fires_pc hf
                  rw [hpc]
                  exact hlt' (by rw [hs]; exact ptc_mem b0 j)
                · exact absurd hk' (hnc a sp)
            · cases hsel : ProA.selTail Q L g v d'' with
              | some dt' =>
                rw [Code.enter_some (i := Sum.inl dt')
                  (by simp [Code.gatedExit, hxo, hsel])] at he''
                simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq,
                  true_and] at he''
                obtain ⟨rfl, -⟩ := he''
                trivial
              | none =>
                rw [Code.enter_some (i := Sum.inr ())
                  (by simp [Code.gatedExit, hxo, hsel])] at he''
                simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq,
                  true_and] at he''
                obtain ⟨rfl, -⟩ := he''
                trivial
          · rw [next_tail] at hn
            obtain ⟨τ', -, he''⟩ := mm_some hn
            simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq, true_and] at he''
            obtain ⟨rfl, -⟩ := he''
            trivial
          · exact hJ.elim
      · exact hJ.elim

/-! ### The consumers -/

/-- **The half of the slot a prologue copy of block `b` fills is the warp's**: bit 0 of the warp
index. -/
theorem pro_half (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) {k : Nat} (hk : k < (X.tr g).length) {tm : Nat} {bw : Value}
    {d : ProA.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread Q L) X g k = some (some (.inr ⟨.inl (.dp tm bw), .inl d⟩, n)))
    {b : Fin 3} {j : Fin 4} (hs : d.site = .ptc b j) :
    Proof.ProA.half d.dt b = g % L.block / 32 % 2 := by
  have hb : L.block = 256 := hp.block
  have hP : _ ∧ _ := pso_inv hp hX hg k hk _ hσ
  have hi12 : 4 * b.val + j.val < 12 := by omega
  have hold : d.site.old = Proof.ProA.ptcSite (4 * b.val + j.val) := by rw [hs]; exact ptc_old b j
  have hm := Proof.ProA.ptcSite_after hi12
  rw [← hold, show (4 * b.val + j.val) / 4 = b.val by omega] at hm
  have h := hP.1 b.val b.isLt hm
  have hw : g % L.block / 32 < 2 ^ 32 := by
    have := Nat.mod_lt g (show 0 < L.block by omega)
    omega
  unfold Proof.ProA.half
  rw [h, Proof.ProA.shW_of (Proof.Raw.word32Of_b32 _), Nat.mod_eq_of_lt hw]

/-- **A prologue copy site fires once** along a thread. -/
theorem pro_copy_once (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {k1 k2 : Nat} {e1 e2 : Event} (he1 : X.get (g, k1) = some e1)
    (he2 : X.get (g, k2) = some e2) (hc1 : IsCopy e1) (hc2 : IsCopy e2)
    {tm tm' : Nat} {bw bw' : Value} {d1 d2 : ProA.D} {n1 n2 : Cls → Nat}
    (hσ1 : Frame.stateAt (thread Q L) X g k1 =
      some (some (.inr ⟨.inl (.dp tm bw), .inl d1⟩, n1)))
    (hσ2 : Frame.stateAt (thread Q L) X g k2 =
      some (some (.inr ⟨.inl (.dp tm' bw'), .inl d2⟩, n2)))
    (hs : d1.site = d2.site) : k1 = k2 := by
  have hg := Frame.lt_of_get hX he1
  have hpc : ∀ {k : Nat} {e : Event} {tm : Nat} {bw : Value} {d : ProA.D} {n : Cls → Nat},
      X.get (g, k) = some e → Frame.stateAt (thread Q L) X g k =
        some (some (.inr ⟨.inl (.dp tm bw), .inl d⟩, n)) → e.pc = d.site.pc := by
    intro k e tm bw d n he hσ
    obtain ⟨t, ins, o, hat, hi, hc, hf⟩ :=
      Frame.fired_site (fun g hg => thread_sound hp hg) hX he hσ
    exact fires_pc hf
  have key : ∀ {ka kb : Nat} {ea eb : Event} {tma tmb : Nat} {bwa bwb : Value} {da db : ProA.D}
      {na nb : Cls → Nat}, X.get (g, ka) = some ea → X.get (g, kb) = some eb → IsCopy ea →
      Frame.stateAt (thread Q L) X g ka =
        some (some (.inr ⟨.inl (.dp tma bwa), .inl da⟩, na)) →
      Frame.stateAt (thread Q L) X g kb =
        some (some (.inr ⟨.inl (.dp tmb bwb), .inl db⟩, nb)) →
      da.site = db.site → ¬ ka < kb := by
    intro ka kb ea eb tma tmb bwa bwb da db na nb hea heb hca hσa hσb hs hlt
    have hkb : kb < (X.tr g).length := (List.getElem?_eq_some_iff.mp heb).1
    have hP : _ ∧ _ := pso_inv hp hX hg kb hkb _ hσb
    have hmem : ea ∈ (X.tr g).take kb :=
      List.mem_iff_getElem?.mpr ⟨ka, by rw [List.getElem?_take_of_lt hlt]; exact hea⟩
    have := hP.2 ea hmem hca
    rw [hpc hea hσa, hs] at this
    exact lt_irrefl _ this
  rcases Nat.lt_trichotomy k1 k2 with h | h | h
  · exact absurd h (key he1 he2 hc1 hσ1 hσ2 hs)
  · exact h
  · exact absurd h (key he2 he1 hc2 hσ2 hσ1 hs.symm)

end
end PTX.Kernels.InklingRelDecode.Proof2
