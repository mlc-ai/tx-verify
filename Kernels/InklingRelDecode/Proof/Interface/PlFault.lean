-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.ClassFault
public import Kernels.InklingRelDecode.Proof.Interface.Lk2Role
public import Kernels.InklingRelDecode.Proof.Interface.ScRead
public import Kernels.InklingRelDecode.Proof.Thread.FootRole
public import Kernels.InklingRelDecode.Proof.Interface.Lk2NumPre
public import Kernels.InklingRelDecode.Proof.Interface.ShapeLoaderPage
public import Kernels.InklingRelDecode.Proof.Interface.PshWarp
public import Kernels.InklingRelDecode.Proof.Interface.IpTmZero

@[expose] public section

/-!
# The machines do not reject a followed event, except in the softmax region and the epilogue

`Safety.Protocol.faultFree` asks that `next s e ≠ none` at every event `e` of a thread that has a
later event, at the state `s` before it. `next` is `none` only where the machine's rule rejects
the event: an event of another kind than the site's, or a value outside the rule's domain (a read
of bytes that do not rebuild, a float operation outside its domain). The followed event is
fired from the state with a continuation (`fired_of_followed`), so it has the kind of the site.

The statements below prove the field for the states of the common start, the prologue, the worker
(`ld0`, `shfl`, `ldRole` and the sites whose successor does not read the event), the idle roles,
the loader, the MMA warp, the exit role and the epilogue's sites but three. The value-dependent
reads are the base word (`BaseWordRead`), the role byte (`RoleReads`) and `num_iters`
(`NumWordRead`). `FaultRest` is the same statement for the softmax region's states and for the
epilogue's `wait`, `shfl` and `waitLd` (the softmax region's bias bytes, tile words and sum
update, the epilogue's zero test, reciprocal, received word and 64-word load are value facts
proved after tracking: `Lk.faultRest_of`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **The worker's shuffle** fires a shuffle event. -/
theorem worker_shfl_shape (hpre : Pre Q L mem0) {w : Worker.D} {e : Event} {u : TState}
    (hs : w.site = .shfl)
    (hF : (WComp.code L g Q).toMachine.Fired (some (.worker w)) e (some u)) :
    ∃ pc mode av bv cv recv ok, e = ⟨pc, .shfl mode av bv cv recv ok⟩ := by
  obtain ⟨t, hgood, hfire⟩ := hF
  obtain ⟨hat, hinv⟩ := hgood
  have hinv' : (WComp.code L g Q).inv (.worker w) := hinv
  obtain ⟨ins, hc, -, -⟩ := (WComp.stepAt hpre (.worker w)).site hinv'
  obtain ⟨site, P⟩ := w
  simp only at hs
  subst hs
  have hc' : kernel.code[Worker.Site.pc .shfl]? = some ins := hc
  have hins := Option.some.inj (hc'.symm.trans Flow.code_shfl_0)
  have hf : Fires (Worker.Site.pc .shfl) (eventTmpl Loader.asms L g t ins.op) e (some u) := by
    have := hfire
    simp only [Code.toMachine, Code.tmpl] at this
    have hat' : t.pc = Worker.Site.pc .shfl := hat.1
    rw [hat'] at this
    have hc2 : kernel.code[WComp.pc (WComp.WSt.worker ⟨.shfl, P⟩)]? = some ins := hc
    rw [hc2] at this
    exact this
  rw [hins] at hf
  obtain ⟨av, bv, cv, recv, ok, rfl, -⟩ := fires_shfl (p := none) hf
  exact ⟨_, _, av, bv, cv, recv, ok, rfl⟩

/-- **The idle roles** never reject an event. -/
theorem idle_followed {d : Worker.Idle.D} (e : Event) :
    (threadCode L g Q).next (.w (.idle d)) e ≠ none := by
  obtain ⟨site, P⟩ := d
  intro h
  rw [next_w] at h
  cases site <;> simp [WComp.next, Worker.Idle.next] at h


section Followed

variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hf : ThreadFacts Q L mem0 X)
include hpre hX hf

/-- **The common start** does not reject a followed event, if every read of the base word returns
the zero word. -/
theorem dstart_followed (hb : BaseWordRead L X) {k : Nat} {d : DStart.D} {e e' : Event}
    (hg : g < L.threads) (he : (X.tr g)[k]? = some e) (he' : (X.tr g)[k + 1]? = some e')
    (hσ : St Q L X g k = some (some (.d (.dstart d)))) :
    (threadCode L g Q).next (.d (.dstart d)) e ≠ none := by
  obtain ⟨u, hF⟩ := fired_of_followed hf.sound hX hg he he' hσ
  have hsh := DStart.shape_of_pre hpre (fired_dstart hF)
  have hrb : d.site = .ld0 → ∀ pc ac bs, e = ⟨pc, .rd ac bs⟩ → ∃ v, rebuild 3 bs = .ok v := by
    intro hs pc ac bs he2
    have hs' := hsh
    unfold DStart.Shape at hs'
    rw [hs] at hs'
    obtain ⟨ac', bs', he3, hl, hz, -⟩ := hs'
    rw [he2] at he3
    simp only [Event.mk.injEq, Kind.rd.injEq] at he3
    obtain ⟨-, rfl, rfl⟩ := he3
    have hz' := hb (show X.get (g, k) = some ⟨pc, .rd ac bs⟩ by rw [← he2]; exact he) hl hz
    rw [hz']
    exact ⟨_, rebuild_b32 0⟩
  have h1 := dstart_next_ne_none hsh hrb
  intro h
  apply h1
  rw [next_d] at h
  simpa [DComp.next, DComp.dstartNext] using h

/-- **The MMA warp** does not reject a followed event, if every read of `num_iters` returns its
word (and every read of the base word the zero word, for `words_inv`). -/
theorem mma_followed (hb : BaseWordRead L X) (hn : NumWordRead Q L X) (hB : Mma.MmaBcast L X)
    {k : Nat} {d : Mma.D}
    {P : Loader.Pro} {e e' : Event} (hg : g < L.threads) (he : (X.tr g)[k]? = some e)
    (he' : (X.tr g)[k + 1]? = some e')
    (hσ : St Q L X g k = some (some (.w (.mma d P)))) :
    (threadCode L g Q).next (.w (.mma d P)) e ≠ none := by
  obtain ⟨u, hF⟩ := fired_of_followed hf.sound hX hg he he' hσ
  obtain ⟨t', hgd, hfire⟩ := hF
  have hF' : (WComp.code L g Q).toMachine.Fired (some (.mma d P)) e (some u) :=
    ⟨t', ⟨hgd.1, hgd.2.2⟩, hfire⟩
  have hsh := EvW.mma_shape hpre hg hF'
  have hrb : d.site = .ldNum → ∀ pc ac bs, e = ⟨pc, .rd ac bs⟩ → ∃ v, rebuild 3 bs = .ok v := by
    intro hs pc ac bs he2
    have hs' := hsh
    unfold EvW.MmShape at hs'
    rw [hs] at hs'
    obtain ⟨ac', bs', he3, hl, hz⟩ := hs'
    rw [he2] at he3
    simp only [Event.mk.injEq, Kind.rd.injEq] at he3
    obtain ⟨-, rfl, rfl⟩ := he3
    have hz' := hn (show X.get (g, k) = some ⟨pc, .rd ac bs⟩ by rw [← he2]; exact he) hσ hs
      hl hz
    rw [hz']
    exact ⟨_, rebuild_b32 _⟩
  have hwd : d.site = .bar0 → Raw.word32Of (Mma.numWord d) ≠ none := by
    intro hs
    have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
    have hw := ((words_inv hpre hX hf hb hn k _ hσ).2.2 (by rw [hs]; decide)
      (by rw [hs]; decide)).2
    rw [hw, Raw.word32Of_b32]
    simp
  have h7 : g % L.block / 32 = 7 := by
    simpa [RoleWarp, Ledger.roleWarp] using
      roleWarp_inv hf.roleWarp k _ (List.getElem?_eq_some_iff.mp he).1.le hσ
  have h1 := mma_next_ne_none hsh hrb hwd (hB g hg h7 e (List.mem_of_getElem? he))
  by_cases hs : d.site = .setMaxRegInc
  · intro h
    rw [next_w] at h
    simp [WComp.next, hs] at h
  · intro h
    apply h1
    rw [next_w] at h
    simp [WComp.next] at h
    exact h

/-- **The loader** does not reject a followed event, if its reads of `num_pre` and `num_iters`
return the CTA's words. -/
theorem loader_followed (hn : NumWordRead Q L X) (hp : NumPreRead Q L X) {k : Nat}
    {d : Loader.D} {P : Loader.Pro} {e e' : Event}
    (hg : g < L.threads) (he : (X.tr g)[k]? = some e) (he' : (X.tr g)[k + 1]? = some e')
    (hσ : St Q L X g k = some (some (.w (.loader d P)))) :
    (threadCode L g Q).next (.w (.loader d P)) e ≠ none := by
  obtain ⟨u, hF⟩ := fired_of_followed hf.sound hX hg he he' hσ
  obtain ⟨t', hgd, hfire⟩ := hF
  have hF' : (WComp.code L g Q).toMachine.Fired (some (.loader d P)) e (some u) :=
    ⟨t', ⟨hgd.1, hgd.2.2⟩, hfire⟩
  have hr := treach_stateAt hpre hg hσ
  have hsh := EvW.loader_shape hpre hr.2 (hf.ldRng hg hσ) (g := g) (d := d) (P := P) (u := u) hF'
  have hget : X.get (g, k) = some e := he
  have hrb : ∀ pc ac bs, e = ⟨pc, .rd ac bs⟩ → ∃ x, bs = (b32 x).toBytes.map some := by
    intro pc ac bs he2
    subst he2
    have hs' := hsh
    unfold EvW.LdShape at hs'
    have hpage : (d.site = .ldb0 ∨ d.site = .ldb1) → d.i < Q.numIters (ProA.cta L g .z)
        (ProA.cta L g .x) := by
      intro hb
      obtain ⟨t', ins, o, -, hinv, -, -⟩ := Frame.fired_site hf.sound hX hget hσ
      have hinv' : Loader.Inv L g d ∧ Loader.ProEq L g P d ∧ Worker.Rest L g P ∧
          4 ≤ WComp.warpOf L g ∧ g % L.block < 256 := hinv.2
      have hloop := (hf.ldRng hg hσ).loop (by rcases hb with hb | hb <;> rw [hb] <;> rfl)
      have hpg := (page_inv hpre hX hf hn k _ hσ).1
        (by rcases hb with hb | hb <;> rw [hb] <;> rfl)
      omega
    by_cases h0 : d.site = .ld0
    · rw [h0] at hs'
      obtain ⟨ac', bs', he3, hl, hz, -⟩ := hs'
      simp only [Event.mk.injEq, Kind.rd.injEq] at he3
      obtain ⟨-, rfl, rfl⟩ := he3
      exact ⟨_, hp hget hσ h0 hl hz⟩
    by_cases h1 : d.site = .ld1
    · rw [h1] at hs'
      obtain ⟨ac', bs', he3, hl, hz, -⟩ := hs'
      simp only [Event.mk.injEq, Kind.rd.injEq] at he3
      obtain ⟨-, rfl, rfl⟩ := he3
      have hl' : ac.loc = ⟨.shared, g / L.block, L.sharedBase + 212996⟩ := by
        rw [hl, Nat.add_assoc]
      exact ⟨_, hn hget hσ h1 hl' hz⟩
    by_cases hb0 : d.site = .ldb0
    · obtain ⟨pc', ac', bs', he3, hbs⟩ := ldb_word hpre hX hf hg hget hσ (slab := 0)
        (.inl ⟨rfl, hb0⟩) (hpage (.inl hb0))
      simp only [Event.mk.injEq, Kind.rd.injEq] at he3
      obtain ⟨-, -, rfl⟩ := he3
      exact ⟨_, hbs⟩
    by_cases hb1 : d.site = .ldb1
    · obtain ⟨pc', ac', bs', he3, hbs⟩ := ldb_word hpre hX hf hg hget hσ (slab := 1)
        (.inr ⟨rfl, hb1⟩) (hpage (.inr hb1))
      simp only [Event.mk.injEq, Kind.rd.injEq] at he3
      obtain ⟨-, -, rfl⟩ := he3
      exact ⟨_, hbs⟩
    exfalso
    revert hs' h0 h1 hb0 hb1
    cases d.site <;> simp
  have h1 := loader_next_ne_none hsh hrb (hf.ldRng hg hσ)
  by_cases hs : d.site = .setMaxInc
  · intro h
    rw [next_w] at h
    simp [WComp.next, hs] at h
  · intro h
    apply h1
    rw [next_w] at h
    simp [WComp.next] at h
    exact h

/-- **The worker** does not reject a followed event, if every read of the base word returns the
zero word and every read of a role byte returns a role (`RoleReads`). -/
theorem worker_followed (hb : BaseWordRead L X) (hR : RoleReads L X) {k : Nat} {w : Worker.D}
    {e e' : Event} (hg : g < L.threads) (he : (X.tr g)[k]? = some e)
    (he' : (X.tr g)[k + 1]? = some e')
    (hσ : St Q L X g k = some (some (.w (.worker w)))) :
    (threadCode L g Q).next (.w (.worker w)) e ≠ none := by
  obtain ⟨site, P⟩ := w
  obtain ⟨u, hF⟩ := fired_of_followed hf.sound hX hg he he' hσ
  obtain ⟨t', hgd, hfire⟩ := hF
  have hF' : (WComp.code L g Q).toMachine.Fired (some (.worker ⟨site, P⟩)) e (some u) :=
    ⟨t', ⟨hgd.1, hgd.2.2⟩, hfire⟩
  rw [next_w]
  cases site
  case ld0 =>
    obtain ⟨pc, ac, bs, he2, hl, hz⟩ := worker_ld0_shape hpre (g := g) (w := ⟨.ld0, P⟩) rfl hF'
    subst he2
    have hz' := hb (show X.get (g, k) = some ⟨pc, .rd ac bs⟩ from he) hl hz
    subst hz'
    simp [WComp.next, Worker.next, rebuild_b32]
  case shfl =>
    obtain ⟨pc, mode, av, bv, cv, recv, ok, he2⟩ := worker_shfl_shape hpre (g := g)
      (w := ⟨.shfl, P⟩) rfl hF'
    subst he2
    cases recv <;> simp [WComp.next, Worker.next]
  case ldRole =>
    have hg256 : g % L.block < 256 := by
      have := hpre.block
      rw [this]
      exact Nat.mod_lt _ (by omega)
    obtain ⟨ac, bs, he2, -, -⟩ := Worker.shape_ldRole hpre (w := ⟨.ldRole, P⟩) hg256 rfl hF'
    subst he2
    have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
    have hb1 := Lk.ldRole_b1N hpre hX hf.sound hR hk hσ
    have hg128 : 128 ≤ g % L.block := by
      have := (cls_inv k _ hk hσ).not.mp (fun h => h)
      omega
    obtain ⟨h1, h2, -⟩ := hR g k ac bs hg hg128 he
    have hidx : ∃ x, Ledger.roleIdx bs = some x := by
      rcases hb1 with h | h
      · obtain ⟨i, -, hi⟩ := h1 h
        exact ⟨i, hi⟩
      · exact ⟨3, h2 (by omega)⟩
    obtain ⟨x, hx⟩ := hidx
    rcases Lk.dispatch_cases P bs with ⟨h0, -⟩ | ⟨y, -, hd⟩
    · rw [h0] at hx
      cases hx
    · have hrs : ∀ s, WComp.roleStart L g P s ≠ none := by
        intro s
        unfold WComp.roleStart
        split <;> (try split) <;> (try split) <;> simp
      intro h
      apply hrs ((Worker.roleSite (truncBits 32 y).toNat).getD .bad0)
      simpa [WComp.next, WComp.dispatch, Worker.next, hd] using h
  all_goals simp [WComp.next, Worker.next]

omit hpre in
/-- **The exit role's `ret`** has no followed event: it fires `exit`, which ends the thread. -/
theorem exit_ret_followed {k : Nat} {P : Loader.Pro} {e e' : Event}
    (hg : g < L.threads) (he : (X.tr g)[k]? = some e) (he' : (X.tr g)[k + 1]? = some e')
    (hσ : St Q L X g k = some (some (.w (.exit ⟨.ret, P⟩)))) :
    (threadCode L g Q).next (.w (.exit ⟨.ret, P⟩)) e ≠ none := by
  obtain ⟨u, hF⟩ := fired_of_followed hf.sound hX hg he he' hσ
  obtain ⟨t', hgd, hfire⟩ := hF
  exfalso
  have hc : kernel.code[WComp.pc (WComp.WSt.exit ⟨.ret, P⟩)]? = some ⟨none, .ret⟩ :=
    Flow.code_exit_0
  have hfire' := hfire
  simp only [Code.toMachine, Code.tmpl] at hfire'
  rw [show (TSt.w (WComp.WSt.exit ⟨.ret, P⟩)).pc = WComp.pc (WComp.WSt.exit ⟨.ret, P⟩) from rfl,
    hc] at hfire'
  simp [eventTmpl, Fires] at hfire'

/-- **The epilogue** does not reject a followed event outside its `o_final` poll and its tile
load, if the zero test and the reciprocal are defined and the 64 words rebuild there. -/
theorem epi_followed {k : Nat} {d : Epi.D} {e e' : Event}
    (hg : g < L.threads) (he : (X.tr g)[k]? = some e) (he' : (X.tr g)[k + 1]? = some e')
    (hσ : St Q L X g k = some (some (.d (.epi d))))
    (hrcp : d.site = .wait → d.pr.setpOk = true ∧ (d.sk = false → d.pr.rcpOk = true))
    (hld : d.site = .waitLd → d.loadOk = true)
    (hbc : d.site = .shfl → ∀ pc m av b c recv ok, e = ⟨pc, .shfl m av b c recv ok⟩ →
      recv = b32 d.pr.w) :
    (threadCode L g Q).next (.d (.epi d)) e ≠ none := by
  obtain ⟨u, hF⟩ := fired_of_followed hf.sound hX hg he he' hσ
  have hsh := Epi.shape (by rw [hpre.block]) (fired_epi hF)
  have hw4 : d.pr.w < 4 := by
    obtain ⟨t, -, hi, -⟩ := fired_epi hF
    exact hi.ok.w
  have h1 := epi_next_ne_none hsh hrcp hld hbc hw4
  intro h
  apply h1
  rw [next_d] at h
  simpa [DComp.next] using h

end Followed

/-- The states whose followed events are not covered: the softmax region's, and the epilogue's
`o_final` poll (`wait`, the zero test and the reciprocal), broadcast (`shfl`, the received word's
lane bits) and tile load (`waitLd`, the 64 words rebuild). -/
def FaultOpen : TSt → Prop
  | .d (.sm _) => True
  | .d (.epi d) => d.site = .wait ∨ d.site = .waitLd ∨ d.site = .shfl
  | _ => False

/-- **The open part of `Safety.Protocol.faultFree`**: the thread machine does not reject a followed
event at a softmax state or at the epilogue's `o_final` poll, broadcast or tile load
(`FaultOpen`). -/
def FaultRest (Q : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {s : TSt} {e : Event}, g < L.threads → (X.tr g)[k]? = some e →
    (X.tr g)[k + 1]? ≠ none → St Q L X g k = some (some s) → FaultOpen s →
    (threadCode L g Q).next s e ≠ none

/-- **`Safety.Protocol.faultFree` from `FaultRest`**: the common start, the prologue, the workers,
the idle roles, the loader, the MMA warp and the exit role's `bar` never reject a followed event,
given the base word, the role bytes and `num_iters` that the reads return, and the broadcast word
of warp 7 (`Mma.MmaBcast`). -/
theorem faultFree_of (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
    (hf : ThreadFacts Q L mem0 X) (hb : BaseWordRead L X) (hn : NumWordRead Q L X)
    (hR : RoleReads L X) (hp : NumPreRead Q L X) (hB : Mma.MmaBcast L X)
    (hrest : FaultRest Q L X) :
    ∀ {g k : Nat} {s : TSt} {e : Event}, g < L.threads → (X.tr g)[k]? = some e →
      (X.tr g)[k + 1]? ≠ none → Frame.stateAt (code L Q) X g k = some (some s) →
      (threadCode L g Q).next s e ≠ none := by
  intro g k s e hg he hne hσ
  obtain ⟨e', he'⟩ := Option.ne_none_iff_exists'.mp hne
  have hσ' : St Q L X g k = some (some s) := hσ
  cases s with
  | d s =>
    cases s with
    | dstart d => exact dstart_followed hpre hX hf hb hg he he' hσ'
    | pro d =>
      have hz := tmz_inv hpre hX hf hb hg k _ (le_of_lt (List.getElem?_eq_some_iff.mp he).1) hσ'
      refine pro_followed_ne_none hX hf.sound hg he he' hσ' (pro_not_pelDead hpre hX hf hσ')
        (by rw [hz.2]; rfl) fun hs => ?_
      obtain ⟨hdef, tm, -, hpro⟩ := hf.reach hg hσ'
      have ha : ProA.ArgsOk L g d.dt.pro := by
        rw [hpro]; exact DStart.argsOk_inh hpre hg hdef tm
      have hw : d.dt.pro.w71 = Q.splits := by rw [hpro]; exact DStart.inh_w71 hpre
      obtain ⟨h0, h1, h2⟩ := Mbar.wordsSo_all hpre hX hf k _ hσ'
      have hk : d.site.afterSk = true := by rw [hs]; rfl
      have hm : ProA.WordsMatch Q (ProA.cta L g .z) d.dt :=
        ⟨h0 (by rw [hs]; decide) (by rw [hs]; decide), h1 (Or.inl hk), h2 hk⟩
      exact (ProA.divs_of_wordsOk ha (ProA.wordsOk_of_pre hpre hg ha hw hm)).2
    | sm d => exact hrest hg he hne hσ' trivial
    | epi d =>
      by_cases hw : d.site = .wait ∨ d.site = .waitLd ∨ d.site = .shfl
      · exact hrest hg he hne hσ' hw
      · exact epi_followed hpre hX hf hg he he' hσ' (fun h => absurd (.inl h) hw)
          (fun h => absurd (.inr (.inl h)) hw) (fun h => absurd (.inr (.inr h)) hw)
  | w s =>
    cases s with
    | worker w => exact worker_followed hpre hX hf hb hR hg he he' hσ'
    | idle d => exact idle_followed e
    | loader d P => exact loader_followed hpre hX hf hn hp hg he he' hσ'
    | mma d P => exact mma_followed hpre hX hf hb hn hB hg he he' hσ'
    | exit x =>
      obtain ⟨site, P⟩ := x
      cases site with
      | bar =>
        intro h
        rw [next_w] at h
        simp [WComp.next] at h
      | ret => exact exit_ret_followed hX hf hg he he' hσ'

end
end PTX.Kernels.InklingRelDecode.Proof.Interface
