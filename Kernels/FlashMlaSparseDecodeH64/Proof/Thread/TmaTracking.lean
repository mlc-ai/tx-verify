-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.TmaGatherCounts
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.RingEvents
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.NcInputFootprint

@[expose] public section

/-! # The TMA producer's local transitions and coordinate inputs -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmaTracking

open PTX PTX.Flow PTX.Proof Wg1Tma

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private def ncLength (base dst : Nat) : MemAccess :=
  { kind := .load, space := some .global, sem := .weak, elem := .int .s 32, nc := true,
    addr := ⟨.reg base 64, 0⟩, dsts := [some dst] }

private theorem length_event {g pc addr base dst : Nat} {t : TState} {e : Event}
    {o : Option TState} (hsub : t.sub = 0) (hreg : t.regs base = some (b64 addr))
    (hlt : addr < 2 ^ 64) (hal : addr % 4 = 0) (hnc : ncLoads.contains pc = true)
    (ht : t.pc = pc)
    (hf : Fires pc (eventTmpl Assumptions.all L g t (.mem (ncLength base dst))) e o) :
    ∃ bs, LaunchReads.ReadsLaunchWord e addr bs := by
  have hnc' : Assumptions.all.any (·.ncLoads t.pc) = true := by
    rw [ht]
    exact List.any_eq_true.mpr ⟨Assumptions.ncReadOnly, by simp [Assumptions.all], hnc⟩
  have htmpl := loadTmpl_global_nc (A := Assumptions.all) (L := L) (g := g)
    (t := t) (d := dst) (base := base) (w := 32) hsub hreg hlt (by decide) hal hnc'
  rw [eventTmpl, memTmpl_direct_weakLoad (sp := .global) (base := base) (w := 64)
    rfl rfl rfl rfl rfl] at hf
  change Fires pc (loadTmpl Assumptions.all L g t .global true 32 [dst] base 0) e o at hf
  rw [htmpl] at hf
  obtain ⟨bs, _, he, _⟩ := hf
  exact ⟨bs, congrArg Event.kind he, by rw [he]; exact hnc⟩

/-- A followed length read reads the launch word of its row at the pointer `ptr`. -/
private theorem len_event {g ptr off base dst pc : Nat} {d : D} {e : Event} {o : Option TState}
    (hpc : d.site.pc = pc) (hsub0 : d.site.sub = 0)
    (hcode : kernel.code[pc]? = some ⟨none, .mem (ncLength base dst)⟩)
    (hnc : ncLoads.contains pc = true)
    (hlive : base ∈ (Flow.live pc).filter (fun r => Wg1Tma.tracked.contains r))
    (hval : Wg1Tma.valueOf P L g d base = b64 ((paramWord L off 8 + 4 * eOf L g) % 2 ^ 64))
    (hal : (paramWord L off 8 + 4 * eOf L g) % 2 ^ 64 % 4 = 0) (hword : paramWord L off 8 = ptr)
    (hfit : ptr + 4 * eOf L g < 2 ^ 64)
    (hf : (Machine.machine P L g).Fired (some (.tma d)) e o) :
    ∃ bs, LaunchReads.ReadsLaunchWord e (ptr + 4 * eOf L g) bs := by
  obtain ⟨t, ⟨hat, _⟩, hf⟩ := hf
  change (Wg1Tma.code P L g).AtD d t at hat
  have ht := hat.1.trans hpc
  change Fires t.pc (match kernel.code[d.site.pc]? with
    | some ins => eventTmpl Assumptions.all L g t ins.op
    | none => .ub .pcOutOfRange) e o at hf
  rw [ht, hpc, hcode] at hf
  have hsub : t.sub = 0 := by rw [hat.2.1, Wg1Tma.code_sub, hsub0]
  have hreg := (Wg1Tma.atD_regAt hat hpc hlive).trans (congrArg some hval)
  rw [hword, Nat.mod_eq_of_lt hfit] at hreg hal
  exact length_event hsub hreg hfit hal hnc ht hf

private theorem main_event {g ptr : Nat} {d : D} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hp : P.topkLenBase = some ptr) (hs : d.site = .lenOrig)
    (hf : (Machine.machine P L g).Fired (some (.tma d)) e o) :
    ∃ bs, LaunchReads.ReadsLaunchWord e (ptr + 4 * eOf L g) bs := by
  have hb : eOf L g < P.b := (show Wg1Tma.Inv P L g d from hf.choose_spec.1.2).batch
  have hbase := hpre.topkLenBaseLt ptr hp
  have hspan := (hpre.topkLenAddressable ptr hp).2.2
  exact len_event (base := 3045) (dst := 2962) (by rw [hs]; rfl) (by rw [hs]; rfl) Flow.code_load_17
    (by decide) (by decide +kernel) rfl (Thread.paramAddr_mod4 (Thread.paramWord_80_mod4 hpre) g)
    ((Thread.paramWord_80_some hpre hp).trans (Nat.mod_eq_of_lt hbase)) (by omega) hf

private theorem extra_event {g ptr : Nat} {d : D} {e : Event} {o : Option TState}
    (hpre : Pre P L mem0) (hp : P.extraTopkLenBase = some ptr) (hs : d.site = .lenExtra)
    (hf : (Machine.machine P L g).Fired (some (.tma d)) e o) :
    ∃ bs, LaunchReads.ReadsLaunchWord e (ptr + 4 * eOf L g) bs := by
  have hb : eOf L g < P.b := (show Wg1Tma.Inv P L g d from hf.choose_spec.1.2).batch
  have hbase := hpre.extraTopkLenBaseLt ptr hp
  have hspan := (hpre.extraTopkLenAddressable ptr hp).2.2
  exact len_event (base := 3047) (dst := 2963) (by rw [hs]; rfl) (by rw [hs]; rfl) Flow.code_load_18
    (by decide) (by decide +kernel) rfl (Thread.paramAddr_mod4 (Thread.paramWord_144_mod4 hpre) g)
    ((Thread.paramWord_144_some hpre hp).trans (Nat.mod_eq_of_lt hbase)) (by omega) hf

/-- **The TMA role never stops following an actual event.** Its machine records every word it
reads; the optional lengths come from the launch, and the fixed memory addresses from the actual
events. -/
theorem next_tracked (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X)
    {g i : Nat} {d : D} {e : Event} (hs : (Machine.machine P L g).Sound)
    (he : X.get (g, i) = some e)
    (hd : Frame.stateAt (Machine.code P L) X g i = some (some (.tma d))) :
    Machine.next P L g (.tma d) e ≠ some none := by
  obtain ⟨o, hf⟩ := RingEvents.fired_of_trace hX hs he hd
  have hi : Wg1Tma.Inv P L g d := hf.choose_spec.1.2
  have ha := hi.lenOk
  have hb : eOf L g < P.b := hi.batch
  have hcta : ctaidY L g < P.b := hb
  cases hsite : d.site
  case lenOrig =>
    have hn : paramWord L 80 8 ≠ 0 := by simpa only [hsite, LenOk] using ha
    cases hp : P.topkLenBase with
    | none => exact (hn (Thread.paramWord_80_zero hpre hp)).elim
    | some ptr =>
      obtain ⟨bs, hword⟩ := main_event hpre hp hsite hf
      have hr := LaunchReads.rebuild_main (g := g) hpre hX hb hp he hword
      simp [Machine.next, Wg1Tma.next, hsite, hword.1, hr, Wg1Tma.eOf, Wg0.eOf]
  case lenExtra =>
    have hn : paramWord L 144 8 ≠ 0 := by simpa only [hsite, LenOk] using ha
    cases hp : P.extraTopkLenBase with
    | none => exact (hn (Thread.paramWord_144_zero hpre hp)).elim
    | some ptr =>
      obtain ⟨bs, hword⟩ := extra_event hpre hp hsite hf
      have hr := LaunchReads.rebuild_extra (g := g) hpre hX hb hp he hword
      simp [Machine.next, Wg1Tma.next, hsite, hword.1, hr, Wg1Tma.eOf, Wg0.eOf]
  case elect =>
    cases hk : e.kind <;> simp [Machine.next, Wg1Tma.next, hsite, hk, hcta, Machine.lostElection]
    rename_i m n ld
    by_cases hld : ld = PTX.laneOf L g <;> simp [hld]
  case rawReady =>
    have hk := RingEvents.rawReady_expectTx hpre hsite hf
    have hbuf := hi.buf_eq (by simp [hsite]) (by simp [hsite])
    simp [Machine.next, Wg1Tma.next, hsite, hk, hbuf, ctaOf]
  case coordFree =>
    have hk := RingEvents.validFree_arrive hpre hsite hf
    have hphase := hi.phase_eq (by simp [hsite]) (by simp [hsite])
    simp [Machine.next, Wg1Tma.next, hsite, hk, hphase, ctaOf]
  case issue k =>
    cases hk : e.kind <;> simp [Machine.next, Wg1Tma.next, hsite, hk]
    rename_i address sp
    have hm := (TmaGatherCounts.gather_event_fields hpre hsite hf hk).2.2.1
    have hbuf := hi.buf_eq (by simp [hsite]) (by simp [hsite])
    simp [hm, hbuf]
  case coord k j =>
    obtain ⟨t, ⟨hat, _⟩, hf⟩ := hf
    change (Wg1Tma.code P L g).AtD d t at hat
    change Fires t.pc (match kernel.code[d.site.pc]? with
      | some ins => eventTmpl Assumptions.all L g t ins.op
      | none => .ub .pcOutOfRange) e o at hf
    have hc : kernel.code[d.site.pc]? = some ⟨none, .mem (coordLoad k)⟩ := by
      rw [hsite]
      exact coordLoad_code k j
    rw [hc, hat.1] at hf
    obtain ⟨bs, hk, _⟩ := fires_coord hpre hsite hat hi hf
    rw [hk]
    cases hrb : rebuild 3 bs <;> simp [Machine.next, Wg1Tma.next, hsite, hrb]
  all_goals
    intro h
    simp only [Machine.next, Wg1Tma.next, hsite] at h
    repeat' split at h
    all_goals cases h
    all_goals
      rename_i hk hexit helect
      first | exact hexit trivial | (split at hk; all_goals cases hk)

/-- An actual optional length read stays within its declared global input. -/
theorem length_footprint (hpre : Pre P L mem0) {g : Nat} {d : D} {e : Event}
    {o : Option TState} (hSite : d.site = .lenOrig ∨ d.site = .lenExtra)
    (hFire : (Machine.machine P L g).Fired (some (.tma d)) e o) :
    NcInputEvent P e := by
  have ha := (show Wg1Tma.Inv P L g d from hFire.choose_spec.1.2).lenOk
  have hb := Wg1Mma.eOf_lt_b (g := g) hpre
  rcases hSite with hSite | hSite
  · have hNonNull : paramWord L 80 8 ≠ 0 := by simpa only [hSite, LenOk] using ha
    cases hp : P.topkLenBase with
    | none => exact (hNonNull (Thread.paramWord_80_zero hpre hp)).elim
    | some ptr =>
      obtain ⟨_, hr⟩ := main_event hpre hp hSite hFire
      exact NcInputEvent.mainLength hp hb hr.1
  · have hNonNull : paramWord L 144 8 ≠ 0 := by simpa only [hSite, LenOk] using ha
    cases hp : P.extraTopkLenBase with
    | none => exact (hNonNull (Thread.paramWord_144_zero hpre hp)).elim
    | some ptr =>
      obtain ⟨_, hr⟩ := extra_event hpre hp hSite hFire
      exact NcInputEvent.extraLength hp hb hr.1

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.TmaTracking
