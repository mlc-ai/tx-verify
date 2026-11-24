-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.Copy
public import Kernels.InklingRelDecode.Proof2.Lib.Regions
public import Kernels.InklingRelDecode.Proof.Thread.FootSm
public import Kernels.InklingRelDecode.Proof.Thread.FootQ
public import Lemmas.Flow.WriteSpace
public import Lemmas.Flow.AccessLocal
public import Lemmas.Flow.NotRead
public import Kernels.InklingRelDecode.Proof.Thread.ScSm
public import Kernels.InklingRelDecode.Proof.Thread.FootRole

@[expose] public section

/-! # The shared writes on the role table

`wr_class`: every shared write of a launched thread is one of five kinds (`SWrite`), read off the
state it is fired from: the startup's allocation store of the base word, a prologue query store
into the Q tile, the role word (the prologue's `st8` and the epilogue's `stTab`, with their
values), an element of the pair `(num_pre, num_iters)` (the prologue's `st9`), the softmax
region's scratch word of its warp (`store10`). A write is at a position of `wrPcs`
(`kernel_wr_pcs`); the sites at those positions are listed per site type (`*_wr`), and the first
tree's per-site shape lemmas (`Proof/Thread`) give the footprints. No worker site writes.
`wr_placed` is the corollary the placement classes use: every byte is in a region of the
thread's CTA. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame
open PTX.Kernels.InklingRelDecode.Proof.Safety (InRegions)

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The positions of the program's writes. -/
def wrPcs : List Nat :=
  [11, 526, 532, 538, 544, 550, 556, 562, 568, 570, 571, 2250, 2682] ++
    (List.range 64).map (fun i => 2751 + 3 * (i / 2) + i % 2) ++ [2848]

/-- **The program's writes are at the positions of `wrPcs`.** -/
theorem kernel_wr_pcs : OpPcsFast kernel.code writeOp wrPcs = true := by decide +kernel

/-- **A shared write, by footprint** (the thread `g`'s CTA is `g / L.block`); `E` is what the
allocation's store of the base word knows of its position. -/
inductive SWrite (L : Launch) (g : Nat) (E : Prop) : Acc → List Byte → Prop
  /-- The allocation's store of the base word. -/
  | base {col : Nat} : col < 2 ^ 16 → E →
      SWrite L g E { loc := ⟨.shared, g / L.block, L.sharedBase⟩, size := 4 } (b32 col).toBytes
  /-- A query store: four bytes of the Q tile. -/
  | qtile {a : Acc} {bs : List Byte} : a.loc.space = .shared → a.loc.cta = g / L.block →
      a.size = 4 → L.sharedBase + 196608 ≤ a.loc.addr → a.loc.addr + 4 ≤ L.sharedBase + 212992 →
      SWrite L g E a bs
  /-- The role word, with the prologue's or the epilogue's value. -/
  | role {bs : List Byte} {c : Nat} : (c = 16777730 ∨ c = 50529027) →
      (∃ v, storeValue 32 (b32 c) = .ok v ∧ bs = v.toBytes) →
      SWrite L g E (Proof.EvD.wordAcc ⟨.shared, g / L.block, (L.sharedBase + 213336) % 2 ^ 32⟩)
        bs
  /-- An element of the pair `(num_pre, num_iters)`. -/
  | pair {a : Acc} {bs : List Byte} : a.loc.space = .shared → a.loc.cta = g / L.block →
      a.size = 4 → (a.loc.addr = (L.sharedBase + 212992) % 2 ^ 32 ∨
        a.loc.addr = (L.sharedBase + 212992) % 2 ^ 32 + 4) → SWrite L g E a bs
  /-- The softmax region's scratch word of the thread's warp. -/
  | scratch {bs : List Byte} :
      SWrite L g E (Proof.EvD.wordAcc ⟨.shared, g / L.block,
        L.sharedBase + 212992 + g % L.block / 32 % 4 * 4⟩) bs

local macro "site_none" : tactic =>
  `(tactic| (intro s h; revert h; cases s <;> (try (rename_i j; revert j)) <;> decide +kernel))

theorem startup_wr : ∀ s : Startup.Site, s.pc ∈ wrPcs → s = .alloc ∨ s = .allocWr := by
  intro s h; revert h
  cases s with
  | alloc => intro _; exact .inl rfl
  | allocWr => intro _; exact .inr rfl
  | enter r => cases r <;> decide
  | _ => decide

theorem proA_wr (s : ProA.Site) (h : s.pc ∈ wrPcs) :
    (∃ i j, s = .stq i j) ∨ s = .st8 ∨ ∃ j, s = .st9 j := by
  cases s with
  | stq i j => exact .inl ⟨i, j, rfl⟩
  | st8 => exact .inr (.inl rfl)
  | st9 j => exact .inr (.inr ⟨j, rfl⟩)
  | ld k | el k | init k | arr k | psh k | ldq k =>
    exfalso; revert h; revert k; decide
  | pb b j | lb b j | pel b j | ptc b j =>
    exfalso; revert h; revert j; revert b; decide
  | _ => exfalso; revert h; decide

theorem sm_wr : ∀ s : Proof.Sm.Site, s.pc ∈ wrPcs → s = .store10 := by
  intro s h; revert h; cases s <;> (try (rename_i j; revert j)) <;> decide +kernel

theorem worker_wr : ∀ s : Proof.Worker.Site, s.pc ∈ wrPcs → False := by site_none
theorem idle_wr : ∀ s : Proof.Worker.Idle.Site, s.pc ∈ wrPcs → False := by site_none
theorem loader_wr : ∀ s : Proof.Loader.Site, s.pc ∈ wrPcs → False := by site_none
theorem mma_wr : ∀ s : Proof.Mma.Site, s.pc ∈ wrPcs → False := by site_none
theorem exitsite_wr : ∀ s : Proof.WComp.ExitSite, s.pc ∈ wrPcs → False := by site_none

/-- The prologue's query store `(i, j)` is the flat machine's query store `4 i + j`. -/
theorem stq_old (i : Fin 8) (j : Fin 4) :
    (ProA.Site.stq i j).old = Proof.ProA.stqSite (4 * i.val + j.val) := by
  fin_cases i <;> fin_cases j <;> rfl

/-- **The barrier-0 count at a startup state** before the second barrier. -/
theorem start_c0 (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {e : Event} (he : X.get (g, k) = some e) {s : Startup.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread Q L) X g k = some (some (.inl s, n))) :
    (s.site = .alloc ∨ s.site = .allocWr ∨ s.site = .bar0 → c0 X g k = 0) ∧
      (s.site = .ld0 ∨ s.site = .bar1 → c0 X g k = 1) := by
  have hcn : n (.bar 0) = c0 X g k := by
    have := fcount hσ (.bar 0)
    rw [cls_bar0] at this
    exact this
  rcases early hp hX k (noUb_before hX he) with h0 | ⟨h0, -⟩ | ⟨σ, hσ', hP⟩
  · rw [hσ] at h0; cases h0
  · rw [hσ] at h0; cases h0
  · rw [hσ] at hσ'
    obtain rfl := Option.some.inj (Option.some.inj hσ')
    obtain ⟨site, tm, x, bw⟩ := s
    simp only [EarlyPos] at hP
    constructor
    · rintro (h | h | h) <;> simp only at h <;> subst h <;> simp only at hP <;> omega
    · rintro (h | h) <;> simp only at h <;> subst h <;> simp only at hP <;> omega

/-- **Every shared write of a launched thread is one of the five kinds.** -/
theorem wr_class (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g k pc : Nat} {a : Acc} {bs : List Byte} (he : X.get (g, k) = some ⟨pc, .wr a bs⟩)
    (hsp : a.loc.space = .shared) : SWrite L g (c0 X g k ≤ 1) a bs := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
  cases o with
  | none => exact absurd (fires_none_ends hf) (by simp [Ends])
  | some u =>
    have hev := frag_ev hp hg hJ hat hi hc hf
    have hpc := OpPcsFast.mem kernel_wr_pcs hc (fires_write_op hf rfl)
    obtain ⟨x, n⟩ := σ
    rcases x with st | ⟨_ | r, d⟩
    · rcases startup_wr st.site hpc with hs | hs
      · have h' : Startup.Ev L g st ⟨pc, .wr a bs⟩ := hev
        simp [Startup.Ev, hs] at h'
      · have h' : Startup.Ev L g st ⟨pc, .wr a bs⟩ := hev
        simp only [Startup.Ev, hs] at h'
        obtain ⟨col, hcol, h'⟩ := h'
        simp only [Event.mk.injEq, Kind.wr.injEq] at h'
        obtain ⟨-, rfl, rfl⟩ := h'
        exact .base hcol (by rw [(start_c0 hp hX he hσ).1 (.inr (.inl hs))]; omega)
    · rename_i i
      cases i with
      | dp tm bw =>
        rcases d with d | ⟨_ | _, τ⟩
        · have hx : d.site ≠ .exit := by
            rcases proA_wr d.site hpc with ⟨_, _, hs⟩ | hs | ⟨_, hs⟩ <;> rw [hs] <;> simp
          have hF := ProA.fired_old (P := Startup.inh L g Q tm) hx hat hi.1 hc hf
          rcases proA_wr d.site hpc with ⟨i, j, hs⟩ | hs | ⟨j, hs⟩
          · have hsr : Proof.ProA.SbRoom L := by
              have := hp.sharedRange
              unfold sharedBytes at this
              unfold Proof.ProA.SbRoom
              omega
            have ht : Proof.ProA.tidOf L g < 128 := hi.1.args.tid
            obtain ⟨v, bs', a', -, he', hl, hz, h1, h2⟩ := Proof.ProA.shape_stq_foot
              (m := i.val) (w := j.val) i.isLt j.isLt ht hsr hF
              (by simp only [ProA.D.old, hs, stq_old])
            simp only [Event.mk.injEq, Kind.wr.injEq] at he'
            obtain ⟨-, rfl, rfl⟩ := he'
            exact .qtile (by rw [hl]) (by rw [hl]) hz h1 h2
          · obtain ⟨v, hv, he'⟩ := Proof.ProA.shape_st8 hF (by simp [ProA.D.old, hs, ProA.Site.old])
            simp only [Event.mk.injEq, Kind.wr.injEq] at he'
            obtain ⟨-, rfl, rfl⟩ := he'
            exact .role (.inl rfl) ⟨v, hv, rfl⟩
          · fin_cases j
            · obtain ⟨v, -, he'⟩ := Proof.ProA.shape_st9_0 hF
                (by simp [ProA.D.old, hs, ProA.Site.old])
              simp only [Event.mk.injEq, Kind.wr.injEq] at he'
              obtain ⟨-, rfl, rfl⟩ := he'
              exact .pair rfl rfl rfl (.inl rfl)
            · obtain ⟨v, -, he'⟩ := Proof.ProA.shape_st9_1 hF
                (by simp [ProA.D.old, hs, ProA.Site.old])
              simp only [Event.mk.injEq, Kind.wr.injEq] at he'
              obtain ⟨-, rfl, rfl⟩ := he'
              exact .pair rfl rfl rfl (.inr rfl)
        · cases τ with
          | sm d =>
            have hs := sm_wr d.site hpc
            have hS := Proof.ProA.sharedOk_of_pre hp
            obtain ⟨bs', he'⟩ := Proof.Sm.shape_store10_foot hS (sm_fired hat hi hc hf) hs
            simp only [Event.mk.injEq, Kind.wr.injEq] at he'
            obtain ⟨-, rfl, rfl⟩ := he'
            exact .scratch
          | epi d =>
            have h' : Proof.Epi.Shape L g d ⟨pc, .wr a bs⟩ := hev
            unfold Proof.Epi.Shape at h'
            split at h'
            all_goals first
              | exact h'.elim
              | (simp only [Event.mk.injEq, reduceCtorEq, and_false, exists_false] at h'; done)
              | (obtain ⟨v, hv, h'⟩ := h'
                 simp only [Event.mk.injEq, Kind.wr.injEq] at h'
                 obtain ⟨-, rfl, rfl⟩ := h'
                 first
                   | exact .role (.inr rfl) ⟨v, hv, rfl⟩
                   | exact absurd hsp (by simp [Proof.EvD.wordAcc]))
        · exact hJ.elim
      | worker w =>
        cases d with
        | worker w => exact (worker_wr w.site hpc).elim
        | idle d => exact (idle_wr d.site hpc).elim
        | loader d P => exact (loader_wr d.site hpc).elim
        | mma d P => exact (mma_wr d.site hpc).elim
        | exit x => exact (exitsite_wr x.site hpc).elim
    · exact hJ.elim


/-- **A shared write's bytes are in a region of the thread's CTA.** -/
theorem wr_placed (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g k pc : Nat} {a : Acc} {bs : List Byte} (he : X.get (g, k) = some ⟨pc, .wr a bs⟩)
    (hsp : a.loc.space = .shared) {l : Loc} (hl : a.Covers l) :
    l.cta = g / L.block ∧ l.cta < L.grid ∧ InRegions L l := by
  have hg := Frame.lt_of_get hX he
  have hsr := hp.sharedRange
  unfold sharedBytes at hsr
  obtain ⟨hs1, hc, hlo, hhi⟩ := hl
  have hs2 : l.space = .shared := hs1.trans hsp
  have hw : g % L.block / 32 % 4 < 4 := Nat.mod_lt _ (by omega)
  have hm : ∀ c, c ≤ 213340 → (L.sharedBase + c) % 2 ^ 32 = L.sharedBase + c := fun c hc =>
    Nat.mod_eq_of_lt (by omega)
  have hcta : l.cta = g / L.block := by
    cases wr_class hp hX he hsp with
    | base _ => exact hc
    | qtile _ h _ _ _ => exact hc.trans h
    | role _ _ => exact hc
    | pair _ h _ _ => exact hc.trans h
    | scratch => exact hc
  refine ⟨hcta, by rw [hcta]; exact NamedBar.cta_lt hg, ?_⟩
  cases wr_class hp hX he hsp with
  | base _ =>
    simp only at hlo hhi
    exact .inl ⟨hs2, hlo, hhi⟩
  | qtile _ _ hz h1 h2 =>
    rw [hz] at hhi
    exact .inr (.inr (.inl ⟨hs2, by omega, by omega⟩))
  | role _ _ =>
    simp only [Proof.EvD.wordAcc, hm 213336 (by omega)] at hlo hhi
    exact .inr (.inr (.inr (.inr (.inr ⟨hs2, hlo, hhi⟩))))
  | pair _ _ hz h =>
    rw [hz] at hhi
    rw [hm 212992 (by omega)] at h
    exact .inr (.inr (.inr (.inl ⟨hs2, by omega, by omega⟩)))
  | scratch =>
    simp only [Proof.EvD.wordAcc] at hlo hhi
    by_cases h : l.addr < L.sharedBase + 213000
    · exact .inr (.inr (.inr (.inl ⟨hs2, by omega, h⟩)))
    · exact .inr (.inr (.inr (.inr (.inl ⟨hs2, by omega, by omega⟩))))


/-! ### The shared reads -/

/-- A load of shared memory, or a load through a dynamic address. -/
def sharedLoadOp (op : Op) : Bool :=
  loadSpace op == some .shared || (dynamicAccess op && readOp op)

/-- The positions of the program's shared loads: the base word, the softmax scratch, the role
byte, the loader's pair and the MMA warp's word of the pair. -/
def rdPcs : List Nat := [13, 2252, 2340, 2345, 2423]

/-- **The program's shared loads are at the positions of `rdPcs`.** -/
theorem kernel_rd_pcs : OpPcsFast kernel.code sharedLoadOp rdPcs = true := by decide +kernel

theorem rd_pc {g : Nat} {t : TState} {pc : Nat} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) {a : Acc}
    {bs : List (Option Byte)} (hk : e.kind = .rd a bs) (hsp : a.loc.space = .shared) :
    pc ∈ rdPcs := by
  refine OpPcsFast.mem kernel_rd_pcs hc ?_
  rcases fires_read_loc hf hk with ⟨h, -⟩ | h
  · simp [sharedLoadOp, h, hsp]
  · simp [sharedLoadOp, h, fires_read_op hf hk]

/-- **A shared read at `pc`, by footprint** (the thread `g`'s CTA is `g / L.block`). -/
inductive SRead (L : Launch) (g pc : Nat) (E : Prop) : Acc → Prop
  /-- The startup's load of the base word (`E`: what it knows of its position). -/
  | base {a : Acc} : a.loc = ⟨.shared, g / L.block, L.sharedBase⟩ → a.size = 4 → E →
      SRead L g pc E a
  /-- The dispatch's load of its role byte (warps 4 to 7). -/
  | role {a : Acc} : 4 ≤ g % L.block / 32 → pc = Proof.Worker.Site.ldRole.pc →
      a.loc = ⟨.shared, g / L.block, L.sharedBase + 213332 + g % L.block / 32⟩ → a.size = 1 →
      SRead L g pc E a
  /-- A word of the pair `(num_pre, num_iters)`. -/
  | pair {a : Acc} : a.loc.space = .shared → a.loc.cta = g / L.block → a.size = 4 →
      (a.loc.addr = L.sharedBase + 212992 ∨ a.loc.addr = L.sharedBase + 212992 + 4) →
      SRead L g pc E a
  /-- The softmax region's load of the scratch word `tid % 4`. -/
  | scratch {a : Acc} :
      a.loc = ⟨.shared, g / L.block, L.sharedBase + g % L.block % 4 * 4 + 212992⟩ →
      a.size = 4 → SRead L g pc E a

theorem startup_rd : ∀ s : Startup.Site, s.pc ∈ rdPcs → s = .ld0 := by
  intro s h; revert h
  cases s with
  | ld0 => intro _; rfl
  | enter r => cases r <;> decide
  | _ => decide

theorem proA_rd (s : ProA.Site) (h : s.pc ∈ rdPcs) : False := by
  cases s with
  | ld k | el k | init k | arr k | psh k | ldq k | st9 k =>
    revert h; revert k; decide
  | pb b j | lb b j | pel b j | ptc b j | stq b j =>
    revert h; revert j; revert b; decide
  | _ => revert h; decide

theorem sm_rd : ∀ s : Proof.Sm.Site, s.pc ∈ rdPcs → s = .ldL := by
  intro s h; revert h; cases s <;> (try (rename_i j; revert j)) <;> decide +kernel

theorem epi_rd : ∀ s : Proof.Epi.Site, s.pc ∈ rdPcs → False := by site_none
theorem worker_rd : ∀ s : Proof.Worker.Site, s.pc ∈ rdPcs → s = .ldRole ∨ s = .ld0 := by
  intro s h; revert h; cases s <;> decide +kernel
theorem loader_rd : ∀ s : Proof.Loader.Site, s.pc ∈ rdPcs → s = .ld0 ∨ s = .ld1 := by
  intro s h; revert h; cases s <;> decide +kernel
theorem mma_rd : ∀ s : Proof.Mma.Site, s.pc ∈ rdPcs → s = .ldNum := by
  intro s h; revert h; cases s <;> (try (rename_i j; revert j)) <;> decide +kernel
theorem idle_rd : ∀ s : Proof.Worker.Idle.Site, s.pc ∈ rdPcs → False := by site_none
theorem exitsite_rd : ∀ s : Proof.WComp.ExitSite, s.pc ∈ rdPcs → False := by site_none

/-- **Every shared read of a launched thread is one of the four kinds.** -/
theorem rd_class (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g k pc : Nat} {a : Acc} {bs : List (Option Byte)} (he : X.get (g, k) = some ⟨pc, .rd a bs⟩)
    (hsp : a.loc.space = .shared) : SRead L g pc (c0 X g k = 1) a := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
  have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  cases o with
  | none => exact absurd (fires_none_ends hf) (by simp [Ends])
  | some u =>
    have hev := frag_ev hp hg hJ hat hi hc hf
    have hpc := rd_pc hc hf rfl hsp
    obtain ⟨x, n⟩ := σ
    rcases x with st | ⟨_ | r, d⟩
    · have hs := startup_rd st.site hpc
      have h' : Startup.Ev L g st ⟨pc, .rd a bs⟩ := hev
      simp only [Startup.Ev, hs] at h'
      obtain ⟨ac, bs', h', hl, hz, -⟩ := h'
      simp only [Event.mk.injEq, Kind.rd.injEq] at h'
      obtain ⟨-, rfl, rfl⟩ := h'
      exact .base hl hz ((start_c0 hp hX he hσ).2 (.inl hs))
    · rename_i i
      cases i with
      | dp tm bw =>
        rcases d with d | ⟨_ | _, τ⟩
        · exact (proA_rd d.site hpc).elim
        · cases τ with
          | sm d =>
            have hs := sm_rd d.site hpc
            obtain ⟨ac, bs', he', hl, hz⟩ := Proof.Sm.shape_ldL_foot
              (Proof.ProA.sharedOk_of_pre hp) (sm_fired hat hi hc hf) hs
            simp only [Event.mk.injEq, Kind.rd.injEq] at he'
            obtain ⟨-, rfl, rfl⟩ := he'
            exact .scratch hl hz
          | epi d => exact (epi_rd d.site hpc).elim
        · exact hJ.elim
      | worker w =>
        have hw4 : 4 ≤ g % L.block / 32 := (tm_inv hp hX hg k hlen _ hσ).2
        cases d with
        | worker w =>
          have hs : w.site = .ldRole := by
            rcases worker_rd w.site hpc with h | h
            · exact h
            · have hW := hJ.2.2.1.1
              rw [h] at hW
              simp at hW
          have hF : (Proof.WComp.code L g Q).toMachine.Fired (some (.worker w))
              ⟨pc, .rd a bs⟩ (some u) := by
            refine ⟨t, ⟨hat, hi⟩, ?_⟩
            have hc' : kernel.code[(Proof.WComp.code L g Q).pc (.worker w)]? = some ins := hc
            show Fires t.pc ((Proof.WComp.code L g Q).tmpl (some (.worker w)) t) _ (some u)
            simp only [Code.tmpl]
            rw [hc', hat.1]
            exact hf
          have hb : g % L.block < 256 := by
            have := hp.block
            exact this ▸ Nat.mod_lt _ (by omega)
          obtain ⟨ac, bs', he', hl, hz⟩ := Proof.Worker.shape_ldRole hp hb hs hF
          simp only [Event.mk.injEq, Kind.rd.injEq] at he'
          obtain ⟨hpc', rfl, rfl⟩ := he'
          exact .role hw4 hpc' hl hz
        | idle d => exact (idle_rd d.site hpc).elim
        | loader d P =>
          have h' : Proof.EvW.LdShapeW Q L g d ⟨pc, .rd a bs⟩ := hev
          rcases loader_rd d.site hpc with hs | hs
          · simp only [Proof.EvW.LdShapeW, hs] at h'
            obtain ⟨ac, bs', h', hl, hz, -⟩ := h'
            simp only [Event.mk.injEq, Kind.rd.injEq] at h'
            obtain ⟨-, rfl, rfl⟩ := h'
            exact .pair (by rw [hl]) (by rw [hl]) hz (.inl (by rw [hl]))
          · simp only [Proof.EvW.LdShapeW, hs] at h'
            obtain ⟨ac, bs', h', hl, hz, -⟩ := h'
            simp only [Event.mk.injEq, Kind.rd.injEq] at h'
            obtain ⟨-, rfl, rfl⟩ := h'
            exact .pair (by rw [hl]) (by rw [hl]) hz (.inr (by rw [hl]))
        | mma d P =>
          have h' : Proof.EvW.MmShape L g d ⟨pc, .rd a bs⟩ := hev
          have hs := mma_rd d.site hpc
          simp only [Proof.EvW.MmShape, hs] at h'
          obtain ⟨ac, bs', h', hl, hz⟩ := h'
          simp only [Event.mk.injEq, Kind.rd.injEq] at h'
          obtain ⟨-, rfl, rfl⟩ := h'
          exact .pair (by rw [hl]) (by rw [hl]) hz (.inr (by rw [hl]))
        | exit x => exact (exitsite_rd x.site hpc).elim
    · exact hJ.elim

/-- **A shared read's bytes are in a region of the thread's CTA.** -/
theorem rd_placed (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g k pc : Nat} {a : Acc} {bs : List (Option Byte)} (he : X.get (g, k) = some ⟨pc, .rd a bs⟩)
    (hsp : a.loc.space = .shared) {l : Loc} (hl : a.Covers l) :
    l.cta = g / L.block ∧ l.cta < L.grid ∧ InRegions L l := by
  have hg := Frame.lt_of_get hX he
  have hsr := hp.sharedRange
  unfold sharedBytes at hsr
  have hbk : L.block = 256 := hp.block
  obtain ⟨hs1, hc, hlo, hhi⟩ := hl
  have hs2 : l.space = .shared := hs1.trans hsp
  have hw : g % L.block % 4 < 4 := Nat.mod_lt _ (by omega)
  have hw8 : g % L.block / 32 < 8 := by
    have := Nat.mod_lt g (show 0 < L.block by omega)
    omega
  have hcta : l.cta = g / L.block := by
    cases rd_class hp hX he hsp with
    | base h _ => rw [hc, h]
    | role _ _ h _ => rw [hc, h]
    | pair _ h _ _ => exact hc.trans h
    | scratch h _ => rw [hc, h]
  refine ⟨hcta, by rw [hcta]; exact NamedBar.cta_lt hg, ?_⟩
  cases rd_class hp hX he hsp with
  | base h hz =>
    simp only [h, hz] at hlo hhi
    exact .inl ⟨hs2, hlo, hhi⟩
  | role h4 _ h hz =>
    simp only [h, hz] at hlo hhi
    exact .inr (.inr (.inr (.inr (.inr ⟨hs2, by omega, by omega⟩))))
  | pair _ _ hz h =>
    rw [hz] at hhi
    exact .inr (.inr (.inr (.inl ⟨hs2, by omega, by omega⟩)))
  | scratch h hz =>
    simp only [h, hz] at hlo hhi
    by_cases h' : l.addr < L.sharedBase + 213000
    · exact .inr (.inr (.inr (.inl ⟨hs2, by omega, h'⟩)))
    · exact .inr (.inr (.inr (.inr (.inl ⟨hs2, by omega, by omega⟩))))

end
end PTX.Kernels.InklingRelDecode.Proof2
