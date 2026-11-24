-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.RoleRun
public import Kernels.Fp16Gemm8192.Proof.Thread.ClcSites
public import Kernels.Fp16Gemm8192.Proof.Thread.Cluster
public import Kernels.Fp16Gemm8192.Proof.Rings

@[expose] public section

/-! # The consumer threads' accumulator polls and arrivals

A consumer thread polls only at its CLC poll and its accumulator poll (`Consumer.wait_site`), and
arrives only at its acknowledgement and its accumulator arrival (`Consumer.arrive_site`). Once per
tile it polls its CTA's full barrier of its accumulator (warp group `tidOf L g / 32 / 4`) with the
parity of its phase `ap`, and arrives on the leader CTA's empty barrier after loading the values.
Along its run the successful polls of each full barrier are the matching arrivals plus the held
accumulator; while it loops, its successful polls of its own full barrier have the parity of its
phase and of being inside a tile (`Consumer.acc_poll_parity`, `Consumer.acc_arrival_budget`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000

namespace Consumer

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- Accumulator `j`'s full barrier in thread `g`'s CTA. -/
abbrev accFull (L : Launch) (g j : Nat) : Loc := Bar.loc L (g / L.block) ⟨.acc, j, true⟩

/-- Accumulator `j`'s empty barrier in the leader CTA of thread `g`'s cluster. -/
abbrev accEmpty (L : Launch) (g j : Nat) : Loc := Bar.loc L (2 * (g / L.block / 2)) ⟨.acc, j, false⟩

/-- Thread `g`'s accumulator: its warp group. -/
abbrev accIdx (L : Launch) (g : Nat) : Nat := tidOf L g / 32 / 4

/-- Thread `g`'s warp group is below three. -/
theorem group_lt (hpre : Pre P L mem0) : tidOf L g / 32 / 4 < 3 := by
  have := hpre.block
  have := Nat.mod_lt g (show 0 < L.block by omega)
  unfold tidOf
  omega

/-- The sites whose instruction uses an mbarrier object. -/
def Site.object : Site → Bool
  | .clcWait | .accWait | .ack | .accArrive => true
  | _ => false

/-- Every other site's instruction uses no mbarrier object. -/
theorem code_object (s : Site) (hs : s.object = false) {ins : Instr}
    (hc : kernel.code[s.pc]? = some ins) : objectOp ins.op = false := by
  cases s <;> simp only [Site.object, Bool.true_eq_false] at hs
  all_goals first
    | (code_at hc; subst hc; rfl)
    | (rename_i j; fin_cases j <;> (code_at hc; subst hc; rfl))
    | (rename_i j i el; fin_cases j <;> fin_cases i <;> fin_cases el <;>
      (code_at hc; subst hc; rfl))

/-- Whether the thread is inside a tile: from the first load to the last commit. -/
def inTile (d : D) : Nat := match d.site with
  | .load _ | .loadWait _ | .accArrive | .drain _ | .barA _ | .store _ _ _ | .barB _
  | .fence _ | .tma _ | .commit _ => 1
  | _ => 0

/-- Whether the thread is still in the task loop. -/
def Site.looping : Site → Bool
  | .finalDrain | .exitArrive | .exitWait | .relinquish | .ldBase | .dealloc | .exit => false
  | _ => true

/-- The accumulator poll names the thread's full barrier and polls with the phase `ap`. -/
theorem accWait_event (hpre : Pre P L mem0) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hs : d.site = .accWait) (hi : Inv d) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    ∃ ok acq sc, e = ⟨d.site.pc, .wait (accFull L g (accIdx L g)) d.ap ok acq sc⟩ := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  have hblk := hpre.block
  have hw := group_lt (g := g) hpre
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs hi h hc hf ⊢
  subst hs
  code_at hc
  subst hc
  have hap : ap < 2 := hi.ap
  have hm := mbarLoc_b32 (L := L) (g := g) (base := 157)
    (a := L.sharedBase + 8 * (tidOf L g / 32 / 4) + 72)
    ((holds_mem h (Flow.mem_factsFrom (by lit_mem))).trans (congrArg some (by cons_values)))
    (by omega) (by omega)
  have hp : t.regs 890 = some (b32 ap) :=
    (holds_mem h (Flow.mem_factsFrom (by lit_mem))).trans (congrArg some (by cons_values))
  obtain ⟨ok, acq, sc, he, -⟩ := fires_wait_at hm
    (show readBits L g t 32 (.reg 890) = .ok (truncBits 32 (BitVec.ofNat 64 ap)) by
      simp [readBits, readReg, hp, b32, bind, Except.bind, pure, Except.pure]) hf
  have hpar : (truncBits 32 (BitVec.ofNat 64 ap)).toNat % 2 = ap := by
    rcases (by omega : ap = 0 ∨ ap = 1) with rfl | rfl <;> decide
  have hl : (⟨.shared, g / L.block, L.sharedBase + 8 * (tidOf L g / 32 / 4) + 72⟩ : Loc) =
      accFull L g (accIdx L g) := by
    simp only [Bar.loc, Bar.off, Loc.mk.injEq, true_and, accIdx]; omega
  exact ⟨ok, acq, sc, by rw [he, hpar, hl]⟩

/-- The accumulator arrival names the leader CTA's empty barrier of the thread's accumulator. -/
theorem accArrive_event (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState} (hs : d.site = .accArrive)
    (h : Holds t.regs (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    ∃ rel sc, e = ⟨d.site.pc, .arrive (accEmpty L g (accIdx L g)) 0 1 rel sc⟩ := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  have hblk := hpre.block
  have hcta := cta_lt hpre hg
  have hw := group_lt (g := g) hpre
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  code_at hc
  subst hc
  have hm := mbarClusterLoc_ptr (base := 433) (cta := 2 * (g / L.block / 2))
    (a := L.sharedBase + 8 * (tidOf L g / 32 / 4) + 88)
    ((holds_mem h (Flow.mem_factsFrom (by lit_mem))).trans (congrArg some (by cons_values))) hg
    (by rw [hpre.grid] at hcta ⊢; omega)
    (by simp only [clusterOfCta_eq hpre]; omega) (by omega) (by omega)
  obtain ⟨rel, sc, he, -⟩ := fires_arrive_at (cluster := true) (by simpa using hm)
    (show readBits L g t 32 (.imm 0) = .ok 0 by rfl)
    (show readBits L g t 32 (.imm 1) = .ok 1 by rfl) hf
  have hl : (⟨.shared, 2 * (g / L.block / 2), L.sharedBase + 8 * (tidOf L g / 32 / 4) + 88⟩ :
      Loc) = accEmpty L g (accIdx L g) := by
    simp only [Bar.loc, Bar.off, Loc.mk.injEq, true_and, accIdx]; omega
  exact ⟨rel, sc, by rw [he, hl]; rfl⟩

/-- The CLC poll names the thread's CTA's CLC response barrier, with the parity of `cp`. -/
theorem clcWait_event (hpre : Pre P L mem0) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hs : d.site = .clcWait) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    ∃ p ok acq sc, p % 2 = d.cp % 2 ∧
      e = ⟨d.site.pc, .wait ⟨.shared, g / L.block, L.sharedBase + 104⟩ p ok acq sc⟩ := by
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  code_at hc
  subst hc
  have hb : t.regs 140 = some (b32 (L.sharedBase + 104)) :=
    (holds_mem h (Flow.mem_factsFrom (by lit_mem))).trans (congrArg some (by cons_values))
  have hp : t.regs 889 = some (b32 cp) :=
    (holds_mem h (Flow.mem_factsFrom (by lit_mem))).trans (congrArg some (by cons_values))
  obtain ⟨ok, acq, sc, he⟩ := clcWait_fire hpre hb hp hf
  rw [clcResp_loc] at he
  refine ⟨_, ok, acq, sc, ?_, he⟩
  rw [Nat.mod_mod, truncBits_parity]

/-- The consumer thread polls at its CLC poll and at its accumulator poll (its full barrier, with
the phase `ap`). -/
theorem wait_site (hpre : Pre P L mem0) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hi : Inv d) (h : Holds t.regs (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o)
    {m : Loc} {p : Nat} {ok acq : Bool} {sc : MbarScope} (hk : e.kind = .wait m p ok acq sc) :
    (d.site = .accWait ∧ m = accFull L g (accIdx L g) ∧ p = d.ap) ∨
    (d.site = .clcWait ∧ m.addr = L.sharedBase + 104 ∧ p % 2 = d.cp % 2) := by
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  cases hs : site.object
  · exact absurd (by rw [hk]; trivial) (notObject_of_op (code_object site hs hc) hf)
  cases site <;> simp only [Site.object, Bool.false_eq_true] at hs
  · -- the CLC poll
    obtain ⟨p', ok', acq', sc', hp', he⟩ := clcWait_event hpre rfl h hc hf
    rw [he] at hk; simp only [Kind.wait.injEq] at hk
    obtain ⟨rfl, rfl, -⟩ := hk
    exact .inr ⟨rfl, rfl, hp'⟩
  · -- the acknowledgement arrives
    code_at hc
    subst hc
    rcases fires_mbarArrive_kind hf with ⟨_, _, _, _, _, h'⟩ | ⟨_, h'⟩ <;> rw [hk] at h' <;>
      cases h'
  · -- the accumulator poll
    obtain ⟨ok', acq', sc', he⟩ := accWait_event hpre rfl hi h hc hf
    rw [he] at hk; simp only [Kind.wait.injEq] at hk
    obtain ⟨rfl, rfl, -⟩ := hk
    exact .inl ⟨rfl, rfl, rfl⟩
  · -- the accumulator arrival
    code_at hc
    subst hc
    rcases fires_mbarArrive_kind hf with ⟨_, _, _, _, _, h'⟩ | ⟨_, h'⟩ <;> rw [hk] at h' <;>
      cases h'

/-- The consumer thread arrives at its acknowledgement and at its accumulator arrival (the
leader CTA's empty barrier of its accumulator). -/
theorem arrive_site (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {t : TState} {ins : Instr}
    {e : Event} {o : Option TState} (h : Holds t.regs (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o)
    {m : Loc} {tx c : Nat} {rel : Bool} {sc : MbarScope} (hk : e.kind = .arrive m tx c rel sc) :
    (d.site = .accArrive ∧ m = accEmpty L g (accIdx L g)) ∨
    (d.site = .ack ∧ m.addr = L.sharedBase + 128) := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hal := hpre.sharedAlignment
  have hblk := hpre.block
  have hcta := cta_lt hpre hg
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  cases hs : site.object
  · exact absurd (by rw [hk]; trivial) (notObject_of_op (code_object site hs hc) hf)
  cases site <;> simp only [Site.object, Bool.false_eq_true] at hs
  · code_at hc
    subst hc
    rcases fires_mbarWait_kind hf with ⟨_, _, _, _, _, h'⟩ | ⟨_, h'⟩ <;> rw [hk] at h' <;> cases h'
  · -- the acknowledgement
    code_at hc
    subst hc
    have hm := mbarClusterLoc_ptr (base := 149) (cta := 2 * (g / L.block / 2))
      (a := L.sharedBase + 128)
      ((holds_mem h (Flow.mem_factsFrom (by lit_mem))).trans (congrArg some (by cons_values))) hg
      (by rw [hpre.grid] at hcta ⊢; omega)
      (by simp only [clusterOfCta_eq hpre]; omega) (by omega) (by omega)
    exact .inr ⟨rfl, by
      rw [fires_arrive_loc (cluster := true) (by simpa using hm) hf _ _ _ _ _ hk]⟩
  · code_at hc
    subst hc
    rcases fires_mbarWait_kind hf with ⟨_, _, _, _, _, h'⟩ | ⟨_, h'⟩ <;> rw [hk] at h' <;> cases h'
  · -- the accumulator arrival
    obtain ⟨rel', sc', he⟩ := accArrive_event hpre hg rfl h hc hf
    rw [he] at hk; simp only [Kind.arrive.injEq] at hk
    exact .inl ⟨rfl, hk.1.symm⟩

/-- Off the start, the accumulator poll and arrival and the commits, a step keeps the phase,
the held accumulator and being inside a tile, and does not re-enter the task loop. -/
theorem next_frame {c c' : D} {e : Event} (hs : c.site ≠ .setMaxReg) (hs' : c.site ≠ .accWait)
    (hs'' : c.site ≠ .accArrive) (hs''' : ∀ k, c.site ≠ .commit k)
    (hn : next L g c e = some (some c')) :
    c'.ap = c.ap ∧ holds c' = holds c ∧ inTile c' = inTile c ∧ c'.site ≠ .setMaxReg ∧
      (c'.site.looping = true → c.site.looping = true) := by
  obtain ⟨site, m, n, m', n', cp, ap, resp, x, acc, base⟩ := c
  simp only at hs hs' hs'' hs'''
  cases site
  all_goals (try exact absurd rfl hs)
  all_goals (try exact absurd rfl hs')
  all_goals (try exact absurd rfl hs'')
  all_goals (try exact absurd rfl (hs''' _))
  all_goals simp only [next] at hn
  all_goals repeat' (first | split_ifs at hn | split at hn)
  all_goals (try simp only [Option.some.injEq, reduceCtorEq] at hn)
  all_goals (try (simp only [Option.map_eq_some_iff, Option.some.injEq] at hn; obtain ⟨_, -, rfl⟩ :=
    hn))
  all_goals (try subst hn)
  all_goals simp [holds, inTile, Site.looping]

/-- The accumulator counts of a consumer's run: the successful polls of each full barrier are
the arrivals on the matching empty barrier plus the held accumulator; while it loops, the
successful polls of its own full barrier have the parity of its phase and of being inside a
tile; and it starts with phase 0. -/
def ConsRel (L : Launch) (g : Nat) (c : D) (es : List Event) : Prop :=
  (∀ j, j < 2 → okPolls (accFull L g j) es =
      arrivals (accEmpty L g j) es + (if j = accIdx L g then holds c else 0)) ∧
  (accIdx L g < 2 → c.site.looping = true →
    okPolls (accFull L g (accIdx L g)) es % 2 = (c.ap + inTile c) % 2) ∧
  (c.site = .setMaxReg → c.ap = 0)

set_option maxHeartbeats 4000000 in
/-- One step of a consumer's run keeps the accumulator counts. -/
theorem consRel_step (hpre : Pre P L mem0) (hg : g < L.threads) {c c' : D} {pre : List Event}
    {e : Event} {t : TState} {ins : Instr} {o : Option TState} (hq : ConsRel L g c pre)
    (hi : Inv c) (h : Holds t.regs (facts L g c)) (hc : kernel.code[c.site.pc]? = some ins)
    (hf : Fires c.site.pc (eventTmpl Prod L g t ins.op) e o)
    (hn : next L g c e = some (some c')) : ConsRel L g c' (pre ++ [e]) := by
  obtain ⟨hA, hB, hS⟩ := hq
  have hap : c.ap < 2 := hi.ap
  have hP : ∀ j, j < 2 → okPoll (accFull L g j) e = true → c.site = .accWait ∧ j = accIdx L g := by
    intro j hj hok
    obtain ⟨p, acq, sc, hk⟩ := okPoll_wait_form hok
    rcases wait_site hpre hi h hc hf hk with ⟨h1, hl, -⟩ | ⟨-, hl, -⟩
    · exact ⟨h1, by have := congrArg Loc.addr hl; simp only [Bar.loc, Bar.off] at this; omega⟩
    · simp only [Bar.loc, Bar.off] at hl; omega
  have hR : ∀ j, j < 2 → arrivesOn (accEmpty L g j) e = true →
      c.site = .accArrive ∧ j = accIdx L g := by
    intro j hj har
    obtain ⟨tx, n, rel, sc, hk⟩ := arrivesOn_form har
    rcases arrive_site hpre hg h hc hf hk with ⟨h1, hl⟩ | ⟨-, hl⟩
    · exact ⟨h1, by have := congrArg Loc.addr hl; simp only [Bar.loc, Bar.off] at this; omega⟩
    · simp only [Bar.loc, Bar.off] at hl; omega
  have hP0 : c.site ≠ .accWait → ∀ j, j < 2 → okPoll (accFull L g j) e = false :=
    fun hs j hj => Bool.eq_false_iff.mpr fun h' => hs (hP j hj h').1
  have hR0 : c.site ≠ .accArrive → ∀ j, j < 2 → arrivesOn (accEmpty L g j) e = false :=
    fun hs j hj => Bool.eq_false_iff.mpr fun h' => hs (hR j hj h').1
  obtain ⟨site, m, n, m', n', cp, ap, resp, x, acc, base⟩ := c
  simp only at hA hB hS hP0 hR0 hap hn ⊢
  have hcnt : ∀ j, j < 2 → site ≠ .accWait → site ≠ .accArrive →
      okPolls (accFull L g j) (pre ++ [e]) = okPolls (accFull L g j) pre ∧
      arrivals (accEmpty L g j) (pre ++ [e]) = arrivals (accEmpty L g j) pre := by
    intro j hj h1 h2
    rw [okPolls_snoc, arrivals_snoc, hP0 h1 j hj, hR0 h2 j hj]; simp
  by_cases h0 : site = .setMaxReg
  · subst h0
    simp only [next, Option.some.injEq] at hn; subst hn
    refine ⟨fun j hj => ?_, fun hj _ => ?_, (fun h' => by cases h')⟩
    · rw [(hcnt j hj (by simp) (by simp)).1, (hcnt j hj (by simp) (by simp)).2]
      simpa [holds] using hA j hj
    · rw [(hcnt _ hj (by simp) (by simp)).1]
      simpa [inTile, hS rfl] using hB hj rfl
  by_cases h1 : site = .accWait
  · subst h1
    obtain ⟨ok, acq, sc, rfl⟩ := accWait_event hpre rfl hi h hc hf
    simp only [next, Option.some.injEq] at hn; subst hn
    clear h hc hf hP hR hcnt
    have hpo : ∀ j, j < 2 → okPoll (accFull L g j)
        ⟨Site.accWait.pc, .wait (accFull L g (accIdx L g)) ap ok acq sc⟩ =
          (decide (j = accIdx L g) && ok) := by
      intro j hj
      rw [okPoll_wait rfl]
      by_cases hjw : j = accIdx L g
      · subst hjw; simp
      · have : accFull L g (accIdx L g) ≠ accFull L g j := by
          simp only [Bar.loc, Bar.off, ne_eq, Loc.mk.injEq, true_and]; omega
        simp [this, hjw]
    refine ⟨fun j hj => ?_, fun hj _ => ?_, (fun h' => by cases ok <;> cases h')⟩
    · rw [okPolls_snoc, arrivals_snoc, hpo j hj, hR0 (by simp) j hj]
      have := hA j hj
      by_cases hjw : j = accIdx L g <;> cases ok <;> simp_all [holds]
    · rw [okPolls_snoc, hpo _ hj]
      have := hB hj rfl
      cases ok <;> simp_all [inTile]
      omega
  by_cases h2 : site = .accArrive
  · subst h2
    obtain ⟨rel, sc, rfl⟩ := accArrive_event hpre hg rfl h hc hf
    simp only [next, Option.some.injEq] at hn; subst hn
    clear h hc hf hP hR hcnt
    refine ⟨fun j hj => ?_, fun hj _ => ?_, (fun h' => by cases h')⟩
    · rw [okPolls_snoc, arrivals_snoc, hP0 (by simp) j hj]
      have := hA j hj
      by_cases hjw : j = accIdx L g
      · subst hjw
        simp_all [holds, arrivesOn, sourceArrive]
      · have : accEmpty L g (accIdx L g) ≠ accEmpty L g j := by
          simp only [Bar.loc, Bar.off, ne_eq, Loc.mk.injEq, true_and]; omega
        simp_all [holds, arrivesOn, sourceArrive]
    · rw [okPolls_snoc, hP0 (by simp) _ hj]
      simpa [inTile] using hB hj rfl
  have hc' := fun j hj => hcnt j hj h1 h2
  by_cases h3 : ∃ k, site = .commit k
  · obtain ⟨k, rfl⟩ := h3
    simp only [next] at hn
    split_ifs at hn
    all_goals (simp only [Option.some.injEq] at hn; subst hn)
    all_goals refine ⟨fun j hj => ?_, fun hj hl => ?_, (fun h' => by cases h')⟩
    all_goals (try simp [Site.looping] at hl)
    all_goals (try (rw [(hc' j hj).1, (hc' j hj).2]; simpa [holds] using hA j hj))
    · rw [(hc' _ hj).1]
      simpa [inTile] using hB hj rfl
    · rw [(hc' _ hj).1]
      have := hB hj rfl
      simp only [inTile] at this ⊢
      omega
  · push Not at h3
    obtain ⟨k1, k2, k3, k4, k5⟩ := next_frame (c := ⟨site, m, n, m', n', cp, ap, resp, x, acc,
      base⟩)
      h0 h1 h2 h3 hn
    simp only at k1 k2 k3 k4 k5
    refine ⟨fun j hj => ?_, fun hj hl => ?_, fun h' => absurd h' k4⟩
    · rw [(hc' j hj).1, (hc' j hj).2, k2]
      exact hA j hj
    · rw [(hc' _ hj).1, k1, k3]
      exact hB hj (k5 hl)

/-- The accumulator counts along a thread's run: none in the prologue, `ConsRel` in the
consumer threads. -/
def AccInv (L : Launch) (g : Nat) : ThreadD → List Event → Prop
  | .inl _, es => Quiet es
  | .inr (.cons c), es => ConsRel L g c es
  | _, _ => True

theorem accInv (hpre : Pre P L mem0) (hg : g < L.threads) {es : List Event}
    (htr : (code L g).toMachine.Trace (some (code L g).init) es) :
    ∀ j d, (code L g).toMachine.after (some (code L g).init) (es.take j) = some (some d) →
      AccInv L g d (es.take j) := by
  refine Code.run_inv (sound hpre hg) htr (AccInv L g) quiet_nil ?_
  intro d d' pre e t ins o hq hat hinv hc hf hn
  rcases d with p | (l | m | sd | cs)
  · have hq' := hq.snoc (Prologue.fires_quiet hc hf)
    change Prologue.next L g p e = some (some d') at hn
    rcases d' with p' | (l' | m' | sd' | cs')
    · exact hq'
    all_goals try trivial
    obtain rfl := Prologue.next_cons hn
    refine ⟨fun j _ => ?_, fun _ _ => ?_, fun _ => rfl⟩
    · simp [(hq' _).1, (hq' _).2.1, holds, Prologue.consStart]
    · simp [(hq' _).1, inTile, Prologue.consStart]
  · obtain ⟨l', -, rfl⟩ := next_of_loader hn; trivial
  · obtain ⟨m', -, rfl⟩ := next_of_mma hn; trivial
  · obtain ⟨s', -, rfl⟩ := next_of_sched hn; trivial
  · obtain ⟨c', hc', rfl⟩ := next_of_cons hn
    exact consRel_step hpre hg hq hinv.1 hat.2.2.2.2 hc hf hc'

end Consumer

/-- A consumer thread's poll of its CTA's full barrier of accumulator `j` uses the parity of its
own successful polls on it. -/
theorem Consumer.acc_poll_parity {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat} (hg : g < L.threads)
    {k : Nat} {e : Event} (he : X.get (g, k) = some e) {c : Consumer.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
      some (some (.inr (.cons c))))
    {j p : Nat} {ok acq : Bool} {sc : MbarScope} (hj : j < 2)
    (hk : e.kind = .wait (Consumer.accFull L g j) p ok acq sc) :
    p % 2 = okPolls (Consumer.accFull L g j) ((X.tr g).take k) % 2 := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, o, hat, ⟨hi, -⟩, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  have hap : c.ap < 2 := hi.ap
  rcases Consumer.wait_site hpre hi hat.2.2.2.2 hc hfire hk with ⟨hs, h, rfl⟩ | ⟨-, h, -⟩
  · have hjw : j = Consumer.accIdx L g := by
      have := congrArg Loc.addr h; simp only [Bar.loc, Bar.off] at this; omega
    subst hjw
    have hB := (Consumer.accInv hpre hg htr k _ hσ).2.1 hj (by simp [Consumer.Site.looping, hs])
    simp only [Consumer.inTile, hs, Nat.add_zero] at hB
    omega
  · simp only [Bar.loc, Bar.off] at h
    omega

/-- A consumer thread's arrival on the leader CTA's empty barrier of accumulator `j` follows a
successful poll of its full barrier that no earlier arrival has used. -/
theorem Consumer.acc_arrival_budget {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
    (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) {g : Nat} (hg : g < L.threads)
    {k : Nat} {e : Event} (he : X.get (g, k) = some e) {c : Consumer.D}
    (hσ : (code L g).toMachine.after (some (code L g).init) ((X.tr g).take k) =
      some (some (.inr (.cons c))))
    {j tx n : Nat} {rel : Bool} {sc : MbarScope} (hj : j < 2)
    (hk : e.kind = .arrive (Consumer.accEmpty L g j) tx n rel sc) :
    arrivals (Consumer.accEmpty L g j) ((X.tr g).take k) + 1 ≤
      okPolls (Consumer.accFull L g j) ((X.tr g).take k) := by
  have htr := Frame.trace (fun _ => sound hpre) hX hg
  obtain ⟨t, ins, o, hat, -, hc, hfire⟩ := Frame.fired_site (fun _ => sound hpre) hX he hσ
  rcases Consumer.arrive_site hpre hg hat.2.2.2.2 hc hfire hk with ⟨hs, h⟩ | ⟨-, h⟩
  · have hjw : j = Consumer.accIdx L g := by
      have := congrArg Loc.addr h; simp only [Bar.loc, Bar.off] at this; omega
    subst hjw
    have hA := (Consumer.accInv hpre hg htr k _ hσ).1 _ hj
    simp only [Consumer.holds, hs, ↓reduceIte] at hA
    omega
  · simp only [Bar.loc, Bar.off] at h
    omega

end
end PTX.Kernels.Fp16Gemm8192.Proof
