-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.RoleRead

@[expose] public section

/-! # The workers' roles run at the first iteration only

The dispatch reads its role byte at barrier-1 count 1 or 4 (`w1_inv` with the bounds below). At
count 1 the byte is byte `w - 4` of the prologue's `st8` word `0x01000202` (`role_read1`): 2, 2, 0
or 1, so warps 4 and 5 enter the idle role, warp 6 the loader and warp 7 the MMA warp, and no warp
takes the bad-byte barriers. At count 4 the byte is 3 (`role_readN`), the exit path. So a role
state (idle, loader, MMA) is at barrier-1 count 1, 2 or 3 (`RIt`), entered from the read at count
1, and the loop's head is at count 0 or 3 (`ri_inv`). With `w1_inv` the count of a role state is
its phase (`role_count`): the loader's and the MMA warp's reads of the pair `(num_pre, num_iters)`
are at count 1.

`role_byte` states the two reads for the event at the dispatch's position, and `role_warp` says
which role each warp runs. -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-! ### The role byte's values -/

theorem b32_toBytes (x : Nat) :
    (b32 x).toBytes = [i32Byte x 0, i32Byte x 1, i32Byte x 2, i32Byte x 3] := by
  simp [Value.toBytes, Value.bytes, List.range_succ, i32Byte, b32]

/-- The byte the role word `x` gives warp `w` (4 to 7). -/
theorem role_wbyte {sb c w x : Nat} (hsb : sb + 213340 < 2 ^ 32) (hw4 : 4 ≤ w) (hw8 : w < 8) :
    wbyte (Proof.EvD.wordAcc ⟨.shared, c, (sb + 213336) % 2 ^ 32⟩) (b32 x).toBytes
      ⟨.shared, c, sb + 213332 + w⟩ = some (i32Byte x (w - 4)) := by
  have hmod : (sb + 213336) % 2 ^ 32 = sb + 213336 := Nat.mod_eq_of_lt (by omega)
  have hAj : sb + 213332 + w - (sb + 213336) = w - 4 := by omega
  rw [b32_toBytes]
  simp only [wbyte, Proof.EvD.wordAcc, hmod, hAj]
  rcases (by omega : w - 4 = 0 ∨ w - 4 = 1 ∨ w - 4 = 2 ∨ w - 4 = 3) with h | h | h | h <;>
    rw [h] <;> rfl

theorem storeValue_b32' (x : Nat) : storeValue 32 (b32 x) = .ok (b32 x) :=
  storeValue_of_bytes (by rfl)

/-- The bytes of one loaded byte of a word. -/
theorem rebuild_byte (x j : Nat) (hj : j < 4) :
    rebuild 3 [some (i32Byte x j)] = .ok (Value.bits 8 (BitVec.ofNat 64 (x / 256 ^ j % 256))) := by
  unfold i32Byte
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  all_goals
    simp [rebuild, rebuild.halves, Value.byteAt, intByte, rebuildBits, littleEndianBits,
      byteBits, Value.bitPattern, Value.bytes, Value.toBytes, pure, Except.pure]
    try (congr 1; omega)

/-- **The dispatch on a byte of a word**: the role site of the byte's value. -/
theorem dispatch_byte (P : Proof.Loader.Pro) (x j : Nat) (hj : j < 4) :
    Proof.Worker.dispatch P [some (i32Byte x j)] =
      some (some ⟨(Proof.Worker.roleSite (x / 256 ^ j % 256)).getD .bad0, P⟩) := by
  unfold Proof.Worker.dispatch
  rw [rebuild_byte x j hj]
  have hl : x / 256 ^ j % 256 < 256 := Nat.mod_lt _ (by omega)
  simp only [extendLoaded, Value.bitPattern, MemExt.extendBits, pure, Except.pure]
  rw [Proof.ProA.truncBits_ofNat 8 _ (by decide)]
  simp only [BitVec.toNat_ofNat]
  rw [Proof.ProA.truncBits_ofNat 32 _ (by decide)]
  simp only [BitVec.toNat_ofNat]
  rw [show x / 256 ^ j % 256 % 2 ^ 64 % 2 ^ 8 % 2 ^ 32 % 2 ^ 64 = x / 256 ^ j % 256 by omega]

/-! ### The successors of the roles -/

/-- The role states: the idle role, the loader and the MMA warp. -/
def isRole : Proof.WComp.WSt → Bool
  | .idle _ | .loader _ _ | .mma _ _ => true
  | _ => false

/-- **A role state steps within its role, at a phase other than its last, or returns to the
loop's head.** -/
theorem role_succ {σ σ' : Proof.WComp.WSt} {e : Event} (hr : isRole σ = true)
    (h : Proof.WComp.next L g σ e = some (some σ')) :
    (isRole σ' = true ∧ wph σ ≠ 0) ∨ ∃ P, σ' = .worker ⟨.loop, P⟩ := by
  cases σ with
  | idle d =>
    obtain ⟨s, P⟩ := d
    cases s <;> simp only [Proof.WComp.next, Proof.Worker.Idle.next, Option.map,
      Option.some.injEq] at h <;> subst h
    all_goals first
      | exact .inr ⟨_, rfl⟩
      | exact .inl ⟨rfl, by simp [wph, idPh]⟩
  | loader d P =>
    obtain ⟨s, pro, i, n, p0, p1, ln⟩ := d
    cases s
    all_goals simp only [Proof.WComp.next] at h
    all_goals first
      | (obtain ⟨d', -, rfl⟩ := mm_some h; exact .inl ⟨rfl, by simp [wph, ldPh]⟩)
      | (simp only [Option.some.injEq] at h; exact .inr ⟨_, h.symm⟩)
  | mma d P =>
    obtain ⟨s, i, n, tm, pro⟩ := d
    cases s
    all_goals simp only [Proof.WComp.next] at h
    all_goals first
      | (obtain ⟨d', -, rfl⟩ := mm_some h; exact .inl ⟨rfl, by simp [wph, mmPh]⟩)
      | (simp only [Option.some.injEq] at h; exact .inr ⟨_, h.symm⟩)
  | _ => simp [isRole] at hr

/-- The roles the dispatch enters for a byte below 3 are role states. -/
theorem roleStart_role {P : Proof.Loader.Pro} {i : Nat} (hi : i < 3) {σ' : Proof.WComp.WSt}
    (h : Proof.WComp.roleStart L g P ((Proof.Worker.roleSite i).getD .bad0) = some (some σ')) :
    isRole σ' = true := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  · simp only [Proof.Worker.roleSite, Option.getD_some, Proof.WComp.roleStart,
      Option.some.injEq] at h
    subst h; rfl
  · simp only [Proof.Worker.roleSite, Option.getD_some, Proof.WComp.roleStart] at h
    repeat' split at h
    all_goals simp only [Option.some.injEq, reduceCtorEq] at h
    subst h; rfl
  · simp only [Proof.Worker.roleSite, Option.getD_some, Proof.WComp.roleStart,
      Option.some.injEq] at h
    subst h; rfl

/-! ### The invariant -/

/-- **The barrier-1 count bounds of a worker state**: the loop's head and its barrier at most 3,
the role byte's load at most 4, a role state 1 to 3, the exit path at least 4; the bad-byte
barriers are not reached. -/
def RIt : Proof.WComp.WSt → Nat → Prop
  | .worker w, c => (w.site = .loop → c ≤ 3) ∧ (w.site = .bar2 → c ≤ 3) ∧
      (w.site = .ldRole → c ≤ 4) ∧ w.site ≠ .bad0 ∧ w.site ≠ .bad1
  | .idle _, c => 1 ≤ c ∧ c ≤ 3
  | .loader _ _, c => 1 ≤ c ∧ c ≤ 3
  | .mma _ _, c => 1 ≤ c ∧ c ≤ 3
  | .exit _, c => 4 ≤ c

/-- The bounds on the thread machine's worker states. -/
def RI (Q : Params) (L : Launch) (g : Nat) : (thread Q L g).D → Nat → Prop
  | (.inr ⟨.inl (.worker _), σ⟩, _), c => RIt σ c
  | _, _ => True

theorem isRole_rit {σ : Proof.WComp.WSt} {c : Nat} (h : isRole σ = true) (h1 : 1 ≤ c)
    (h3 : c ≤ 3) : RIt σ c := by
  cases σ <;> simp_all [isRole, RIt]

theorem rit_role {σ : Proof.WComp.WSt} {c : Nat} (h : isRole σ = true) (hR : RIt σ c) :
    1 ≤ c ∧ c ≤ 3 := by
  cases σ <;> simp_all [isRole, RIt]

/-- The dispatch's successor from the read's byte. -/
theorem dispatch_succ {P : Proof.Loader.Pro} {e : Event} {σ' : Proof.WComp.WSt}
    (h : Proof.WComp.next L g (.worker ⟨.ldRole, P⟩) e = some (some σ')) :
    ∃ a bs, e.kind = .rd a bs ∧ ∃ d', Proof.Worker.dispatch P bs = some (some d') ∧
      Proof.WComp.roleStart L g P d'.site = some (some σ') := by
  simp only [Proof.WComp.next, Proof.WComp.dispatch] at h
  rcases hw : Proof.Worker.next L g ⟨.ldRole, P⟩ e with _ | _ | d'
  · rw [hw] at h; cases h
  · rw [hw] at h; cases h
  · rw [hw] at h
    simp only [Proof.Worker.next] at hw
    split at hw
    · rename_i a bs hk
      exact ⟨a, bs, hk, d', hw, h⟩
    · cases hw

/-- The successor of the exit path is the exit path. -/
theorem exit_succ {x : Proof.WComp.ExitD} {e : Event} {σ' : Proof.WComp.WSt}
    (h : Proof.WComp.next L g (.exit x) e = some (some σ')) : ∃ x', σ' = .exit x' := by
  obtain ⟨s, P⟩ := x
  cases s <;> simp only [Proof.WComp.next, Option.some.injEq, reduceCtorEq] at h
  exact ⟨_, h.symm⟩

/-- **The barrier-1 count bounds of the workers along a thread.** -/
theorem ri_inv (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) :
    ∀ k, k < (X.tr g).length → ∀ σ, Frame.stateAt (thread Q L) X g k = some (some σ) →
      RI Q L g σ (((X.tr g).take k).countP (Execution.isBarId 1)) := by
  have hb : L.block = 256 := hp.block
  have hsr := hp.sharedRange
  unfold sharedBytes at hsr
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
    have hσ'0 := hσ'
    rw [Frame.stateAt_succ he] at hσ'
    have hF := good_all' hp hX hg k
    rcases hk0 : Frame.stateAt (thread Q L) X g k with _ | _ | σ
    · rw [hk0] at hσ'; cases hσ'
    · exact absurd hk0 hF.1
    · rw [hk0] at hσ'
      have hn : (thread Q L g).next σ e = some (some σ') := hσ'
      have hJ := hF.2 σ hk0
      have hW0 := w1_inv hp hX hg k hlt σ hk0
      have hW1 := w1_inv hp hX hg (k + 1) hk σ' hσ'0
      have hR0 := ih hlt σ hk0
      rw [List.take_add_one, he, Option.toList_some, countP_snoc] at hW1 ⊢
      set c := ((X.tr g).take k).countP (Execution.isBarId 1) with hcdef
      obtain ⟨x, n⟩ := σ
      rcases x with s | ⟨_ | r, d⟩
      · -- a startup state: the count is 0, and a worker is entered at the loop's head
        rw [next_start] at hn
        obtain ⟨s', -, rfl⟩ := mm_some hn
        simp only [Code.enter]
        split
        · rename_i j _
          rcases j with (_ | _) | _
          · trivial
          · have hc0 : c = 0 := hW0
            refine ⟨fun _ => ?_, fun _ => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
            all_goals first
              | (split <;> omega)
              | (simp at h)
          · trivial
        · trivial
      · rename_i i
        obtain ⟨d', hd'⟩ := next_same_role hn
        obtain ⟨x', n'⟩ := σ'
        simp only at hd'
        subst hd'
        cases i with
        | dp tm bw => trivial
        | worker w =>
          rw [next_worker] at hn
          obtain ⟨σw', hσw, he'⟩ := mm_some hn
          simp only [Prod.mk.injEq, Sum.inr.injEq, heq_eq_eq, Sigma.mk.injEq, true_and] at he'
          obtain ⟨he1, -⟩ := he'
          subst he1
          have hc0 : c % 3 = wph d := hW0
          have hc1 : (c + if Execution.isBarId 1 e = true then 1 else 0) % 3 = wph σw' := hW1
          have hR : RIt d c := hR0
          show RIt σw' (c + if Execution.isBarId 1 e = true then 1 else 0)
          have hWS : WSite (b32 0) d := hJ.2.2.1
          have hb01 : (if Execution.isBarId 1 e = true then 1 else 0) ≤ 1 := by split <;> omega
          by_cases hrole : isRole d = true
          · obtain ⟨h1, h3⟩ := rit_role hrole hR
            rcases role_succ hrole hσw with ⟨hr', hph⟩ | ⟨P', rfl⟩
            · exact isRole_rit hr' (by omega) (by omega)
            · simp only [wph] at hc1
              refine ⟨fun _ => by omega, fun h => by simp at h, fun h => by simp at h,
                fun h => by simp at h, fun h => by simp at h⟩
          · cases d with
            | worker wd =>
              obtain ⟨site, P⟩ := wd
              obtain ⟨hs, -⟩ := hWS
              simp only at hs
              obtain ⟨hl3, hb3, hr4, hn0, hn1⟩ := hR
              simp only at hl3 hb3 hr4 hn0 hn1
              rcases hs with rfl | rfl | rfl | rfl | rfl
              · -- the loop's head steps to its barrier
                simp only [Proof.WComp.next, Proof.Worker.next, Option.map,
                  Option.some.injEq] at hσw
                subst hσw
                have : c ≤ 3 := hl3 rfl
                have h0 : c % 3 = 0 := hc0
                refine ⟨fun h => by simp at h, fun _ => ?_, fun h => by simp at h,
                  fun h => by simp at h, fun h => by simp at h⟩
                simp only [wph] at hc1
                omega
              · -- the barrier steps to the role byte's load
                simp only [Proof.WComp.next, Proof.Worker.next, Option.map,
                  Option.some.injEq] at hσw
                subst hσw
                have : c ≤ 3 := hb3 rfl
                refine ⟨fun h => by simp at h, fun h => by simp at h, fun _ => by omega,
                  fun h => by simp at h, fun h => by simp at h⟩
              · -- the dispatch: the role byte selects the role
                obtain ⟨a, bs, hk, d', hdisp, hst⟩ := dispatch_succ hσw
                obtain ⟨pc, kd⟩ := e
                simp only at hk
                subst hk
                have hget : X.get (g, k) = some ⟨pc, .rd a bs⟩ := he
                have hnb : (if Execution.isBarId 1 (⟨pc, .rd a bs⟩ : Event) = true then 1
                    else 0) = 0 := by simp [Execution.isBarId]
                rw [hnb, Nat.add_zero]
                have hc4 : c ≤ 4 := hr4 rfl
                have hw4 : 4 ≤ g % L.block / 32 := (tm_inv hp hX hg k hlt _ hk0).2
                have hw8 : g % L.block / 32 < 8 := by
                  have := Nat.mod_lt g (show 0 < L.block by omega)
                  omega
                have hph : c % 3 = 1 := hc0
                rcases (by omega : c = 1 ∨ c = 4) with h1 | h4
                · obtain ⟨v, hv, hl, hbs⟩ := role_read1 hp hX hget hk0 h1
                  rw [storeValue_b32'] at hv
                  obtain rfl := (Except.ok.inj hv).symm
                  rw [hl, role_wbyte (by omega) hw4 hw8] at hbs
                  subst hbs
                  rw [dispatch_byte P _ _ (by omega)] at hdisp
                  obtain rfl := Option.some.inj (Option.some.inj hdisp)
                  have hi : 16777730 / 256 ^ (g % L.block / 32 - 4) % 256 < 3 := by
                    rcases (by omega : g % L.block / 32 - 4 = 0 ∨ g % L.block / 32 - 4 = 1 ∨
                      g % L.block / 32 - 4 = 2 ∨ g % L.block / 32 - 4 = 3) with h | h | h | h <;>
                      rw [h] <;> norm_num
                  exact isRole_rit (roleStart_role hi hst) (by omega) (by omega)
                · obtain ⟨v, hv, hl, hbs⟩ := role_readN hp hX hget hk0 (by omega)
                  rw [storeValue_b32'] at hv
                  obtain rfl := (Except.ok.inj hv).symm
                  rw [hl, role_wbyte (by omega) hw4 hw8] at hbs
                  subst hbs
                  rw [dispatch_byte P _ _ (by omega)] at hdisp
                  obtain rfl := Option.some.inj (Option.some.inj hdisp)
                  have hi : 50529027 / 256 ^ (g % L.block / 32 - 4) % 256 = 3 := by
                    rcases (by omega : g % L.block / 32 - 4 = 0 ∨ g % L.block / 32 - 4 = 1 ∨
                      g % L.block / 32 - 4 = 2 ∨ g % L.block / 32 - 4 = 3) with h | h | h | h <;>
                      rw [h] <;> norm_num
                  simp only [hi, Proof.Worker.roleSite, Option.getD_some,
                    Proof.WComp.roleStart, Option.some.injEq] at hst
                  subst hst
                  show 4 ≤ c
                  omega
              · exact absurd rfl hn0
              · exact absurd rfl hn1
            | exit x =>
              obtain ⟨x', rfl⟩ := exit_succ hσw
              have : 4 ≤ c := hR
              show 4 ≤ _
              omega
            | _ => simp [isRole] at hrole
      · exact hJ.elim

/-- **A role state's barrier-1 count is its phase** (1 to 3): the roles run at the first
iteration of the dispatch loop only. -/
theorem role_count (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hg : g < L.threads) {k : Nat} (hk : k < (X.tr g).length) {tm : Value}
    {σ : Proof.WComp.WSt} {n : Cls → Nat} (hr : isRole σ = true)
    (hσ : Frame.stateAt (thread Q L) X g k = some (some (.inr ⟨.inl (.worker tm), σ⟩, n))) :
    ((X.tr g).take k).countP (Execution.isBarId 1) = if wph σ = 0 then 3 else wph σ := by
  have h1 : RIt σ _ := ri_inv hp hX hg k hk _ hσ
  have h2 : _ % 3 = wph σ := w1_inv hp hX hg k hk _ hσ
  obtain ⟨hl, hu⟩ := rit_role hr h1
  split <;> omega

/-! ### The role byte's reads -/

/-- **The role byte's reads**: the event at the dispatch's position is a worker's read of its
role byte at barrier-1 count 1 or at least 4; at count 1 it returns byte `w - 4` of `0x01000202`,
at count 4 or more byte `w - 4` of `0x03030303`. -/
theorem role_byte (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g k : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨Proof.Worker.Site.ldRole.pc, .rd a bs⟩) :
    4 ≤ g % L.block / 32 ∧ g % L.block / 32 < 8 ∧
    (((X.tr g).take k).countP (Execution.isBarId 1) = 1 ∨
      4 ≤ ((X.tr g).take k).countP (Execution.isBarId 1)) ∧
    (((X.tr g).take k).countP (Execution.isBarId 1) = 1 →
      bs = [some (i32Byte 16777730 (g % L.block / 32 - 4))]) ∧
    (4 ≤ ((X.tr g).take k).countP (Execution.isBarId 1) →
      bs = [some (i32Byte 50529027 (g % L.block / 32 - 4))]) := by
  have hb : L.block = 256 := hp.block
  have hsr := hp.sharedRange
  unfold sharedBytes at hsr
  have hg := Frame.lt_of_get hX he
  have hlen : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX he (fun f h => by cases h)
  have hpc : (thread Q L g).pc σ = Proof.Worker.Site.ldRole.pc := (fires_pc hf).symm
  have hmem : (thread Q L g).pc σ ∈ rdPcs := by rw [hpc]; decide
  obtain ⟨x, n⟩ := σ
  rcases x with st | ⟨_ | r, d⟩
  · exfalso
    have hs := startup_rd st.site hmem
    have : st.site.pc = Proof.Worker.Site.ldRole.pc := hpc
    rw [hs] at this
    exact absurd this (by decide)
  · rename_i i
    cases i with
    | dp tm bw =>
      exfalso
      rcases d with d | ⟨_ | _, τ⟩
      · exact proA_rd d.site hmem
      · cases τ with
        | sm d =>
          have hs := sm_rd d.site hmem
          have : d.site.pc = Proof.Worker.Site.ldRole.pc := hpc
          rw [hs] at this
          exact absurd this (by decide)
        | epi d => exact epi_rd d.site hmem
      · exact hJ.elim
    | worker w =>
      have hw4 : 4 ≤ g % L.block / 32 := (tm_inv hp hX hg k hlen _ hσ).2
      have hw8 : g % L.block / 32 < 8 := by
        have := Nat.mod_lt g (show 0 < L.block by omega)
        omega
      have hW0 := w1_inv hp hX hg k hlen _ hσ
      have hR0 := ri_inv hp hX hg k hlen _ hσ
      cases d with
      | worker wd =>
        obtain ⟨site, P⟩ := wd
        have hs : site = .ldRole := by
          rcases worker_rd site hmem with h | h
          · exact h
          · have hW := hJ.2.2.1.1
            simp only at hW
            rw [h] at hW
            simp at hW
        subst hs
        have h1 : _ % 3 = 1 := hW0
        have h4 : _ ≤ 4 := hR0.2.2.1 rfl
        refine ⟨hw4, hw8, by omega, fun hc1 => ?_, fun hc4 => ?_⟩
        · obtain ⟨v, hv, hl, hbs⟩ := role_read1 hp hX he hσ hc1
          rw [storeValue_b32'] at hv
          obtain rfl := (Except.ok.inj hv).symm
          rw [hl, role_wbyte (by omega) hw4 hw8] at hbs
          exact hbs
        · obtain ⟨v, hv, hl, hbs⟩ := role_readN hp hX he hσ hc4
          rw [storeValue_b32'] at hv
          obtain rfl := (Except.ok.inj hv).symm
          rw [hl, role_wbyte (by omega) hw4 hw8] at hbs
          exact hbs
      | idle d =>
        exfalso; exact idle_rd d.site hmem
      | loader d P =>
        exfalso
        have : d.site.pc = Proof.Worker.Site.ldRole.pc := hpc
        rcases loader_rd d.site hmem with hs | hs <;> rw [hs] at this <;>
          exact absurd this (by decide)
      | mma d P =>
        exfalso
        have hs := mma_rd d.site hmem
        have : d.site.pc = Proof.Worker.Site.ldRole.pc := hpc
        rw [hs] at this
        exact absurd this (by decide)
      | exit x => exfalso; exact exitsite_rd x.site hmem
  · exact hJ.elim

end
end PTX.Kernels.InklingRelDecode.Proof2
