-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Data.Values
public import Lemmas.Flow.FloatOutcome
public import Lemmas.Flow.Step.RuleStep
public import Lemmas.Flow.Recip

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (r32 i32 add32 addi sub32 mul32 mad32 min32 shrs shru
  andi scmp scmpi sel addrU addrS xor32 not32 shl popc divOk fdiv Scan laneW paramW
  batchOf skipFirst reqOf tlOf prefixD headsW lanePreds partials chosen loopOf)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (ori ceil128 sbW sbi w32 neg32 wideS)

noncomputable section

/-! ### Transitions -/

/-- Follow a 32-bit word. -/
def word32 (v : Value) (f : BitVec 64 → D) : Option (Option D) :=
  match v with
  | .bits 32 x => some (some (f x))
  | _ => some none

/-- Follow a real `f32` payload. -/
def real32 (v : Value) (f : ℝ → D) : Option (Option D) :=
  match v with
  | .float .f32 x => some (some (f x))
  | _ => some none

/-- The pattern of one reads as one. -/
theorem read_one : Assumption.readEReal .f32 (.bits 32 (BitVec.ofNat 64 1065353216)) =
    some (.ok ((1 : ℝ) : EReal)) := by
  rw [readEReal_bits32 1065353216 1 rfl (by decide) f32Value_one]
  simp

/-- A factor reads as its real number. -/
theorem Sc.read (s : Sc) : Assumption.readEReal .f32 s.val = some (.ok ((s.real : ℝ) : EReal)) := by
  cases s
  · exact readEReal_float_self _ _
  · exact read_one

/-- The pair of the pattern of one reads as a pair of ones. -/
theorem pairRead_one : pairRead (.bits 64 (BitVec.ofNat 64 4575657222473777152)) =
    some (.ok (((1 : ℝ) : EReal), ((1 : ℝ) : EReal))) := by
  have h : splitValue 64 (.bits 64 (BitVec.ofNat 64 4575657222473777152)) =
      (.bits 32 (BitVec.ofNat 64 1065353216), .bits 32 (BitVec.ofNat 64 1065353216)) := rfl
  rw [pairRead, h, read_one]
  rfl

/-- The successor of the factor's load: a number, or the pattern of one. -/
def scale32 (v : Value) (f : Sc → D) : Option (Option D) :=
  match v with
  | .float .f32 x => some (some (f (.num x)))
  | .bits 32 x => if x = BitVec.ofNat 64 1065353216 then some (some (f .one)) else some none
  | _ => some none

@[simp] theorem scale32_val (s : Sc) (f : Sc → D) : scale32 s.val f = some (some (f s)) := by
  cases s <;> simp [scale32]

theorem scale32_some {v : Value} {f : Sc → D} {d : D} (h : scale32 v f = some (some d)) :
    ∃ s : Sc, v = s.val ∧ d = f s := by
  unfold scale32 at h
  split at h
  · cases h; exact ⟨.num _, rfl, rfl⟩
  · split at h
    · rename_i hx
      cases h
      exact ⟨.one, by rw [hx], rfl⟩
    · cases h
  · cases h

theorem scale32_ne_none (v : Value) (f : Sc → D) : scale32 v f ≠ none := by
  unfold scale32
  repeat' split
  all_goals simp

open Classical in
/-- The successor of the row-maximum load: the pattern of an extended real below `+∞`. -/
def max32 (v : Value) (f : Mx → D) : Option (Option D) :=
  if h : ∃ x : Mx, v = Assumption.erealValue .f32 x.1 then some (some (f h.choose)) else some none

theorem max32_ereal (f : Mx → D) (x : Mx) :
    max32 (Assumption.erealValue .f32 x.1) f = some (some (f x)) := by
  have h : ∃ y : Mx, Assumption.erealValue .f32 x.1 = Assumption.erealValue .f32 y.1 := ⟨x, rfl⟩
  have he : h.choose = x := by
    have hr := congrArg (Assumption.readEReal .f32) h.choose_spec
    simp only [readEReal_erealValue_f32, Option.some.injEq, Except.ok.injEq] at hr
    exact Subtype.ext hr.symm
  simp only [max32, dite_eq_left h, he]

theorem max32_fv (f : Mx → D) (x : ℝ) :
    max32 (.float .f32 x) f = some (some (f ⟨x, EReal.coe_ne_top x⟩)) := by
  rw [← max32_ereal, erealValue_coe]

theorem max32_some {v : Value} {f : Mx → D} {d : D} (h : max32 v f = some (some d)) :
    ∃ x : Mx, v = Assumption.erealValue .f32 x.1 ∧ d = f x := by
  unfold max32 at h
  split at h
  · rename_i hx
    exact ⟨_, hx.choose_spec, by simpa using h.symm⟩
  · simp at h

theorem max32_ne_none (v : Value) (f : Mx → D) : max32 v f ≠ none := by
  unfold max32
  split <;> simp

/-- A state at site `s` with the scan state changed by `f`. -/
abbrev scAt (d : D) (s : Site) (f : Epilogue.D → Epilogue.D) : D :=
  D.mk' s { d.v with sc := f d.v.sc }

/-- The end of the scan of pass `late`, with the last group's capped first request `gx` and the
tiles `cur` through it: past the batch, no tile (the final poll); else the ballot. -/
def scanExit (p : Params) (late : Bool) (d : D) (gx cur : BitVec 64) : D :=
  D.ite (scmp .ge .s gx (batchOf p late)) (D.mk' (.wend late) d.v)
    (scAt d (.vote late) fun c => { c with gx := gx, cur := cur })

/-- The loop head of pass `late` with group start `grp` and tiles `acc` before it. -/
def loopHead (p : Params) (L : Launch) (g : Nat) (late : Bool) (d : D) (grp acc : BitVec 64) :
    D :=
  D.ite (scmp .ge .s (addi grp 31) (batchOf p late))
    (scanExit p late d (min32 (addi grp 31) (batchOf p late)) (addi (ctaR p L g) 1))
    (D.ite (scmp .gt .s (reqOf L g grp) (batchOf p late))
      (scAt d (.down (loopOf late)) fun c => { c with grp := grp, acc := acc, w := i32 0 })
      (scAt d (.word (loopOf late)) fun c => { c with grp := grp, acc := acc }))

/-- After lane 31's prefix sum `x` of a round of scan `k`. -/
def afterTotal (p : Params) (L : Launch) (g : Nat) (k : Scan) (d : D) (x : BitVec 64) : D :=
  let d := scAt d d.site fun c => { c with tot := x }
  match k with
  | .first | .second =>
    D.ite (scmp .gt .s (mul32 x (headsW p)) (ctaR p L g))
      (scanExit p k.late d (i32 0) (mul32 x (headsW p)))
      (loopHead p L g k.late d (i32 0) (mul32 x (headsW p)))
  | .loop | .loop2 =>
    D.ite (scmp .le .s (mad32 x (headsW p) d.v.sc.acc) (ctaR p L g))
      (loopHead p L g k.late d (min32 (addi d.v.sc.grp 31) (batchOf p k.late))
        (mad32 x (headsW p) d.v.sc.acc))
      (scanExit p k.late d (min32 (addi d.v.sc.grp 31) (batchOf p k.late))
        (mad32 x (headsW p) d.v.sc.acc))

/-- After the chosen request's tile count `x`: the coordinates, then the request's reads if
the request exists. A division without a rule faults the thread. -/
def afterTiles (p : Params) (L : Launch) (g : Nat) (d : D) (x : BitVec 64) : Option D :=
  let d := scAt d d.site fun c => { c with nt := x }
  let co := coords p L g d.v.sc
  if divOk co.n1 co.d1 then
    if divOk co.n2 co.d2 then
      some (D.ite (scmp .lt .s (chosen d.v.sc) (paramW p.batch)) (D.mk' .q0 d.v)
        (D.mk' (.wend false) d.v))
    else none
  else none

/-- The start of a scheduler pass: lanes past the batch skip their read. -/
def passStart (p : Params) (L : Launch) (g : Nat) (late : Bool) (d : D) : D :=
  let k : Scan := if late then .second else .first
  D.ite (scmp .gt .s (laneW L g) (if late then paramW p.batch else BitVec.ofNat 64 p.batch))
    (scAt d (.down k) fun c => { c with w := i32 0 }) (D.mk' (.word k) d.v)

/-- The rescale rounds on entry: none when the tile has fewer than two blocks. -/
def enterRounds (p : Params) (L : Launch) (g : Nat) (d : D) : D :=
  D.ite (scmpi .lt .s (blocks p L g d.v) 2) (D.mk' .farr0 d.v)
    (D.mk' (.rbar 0) { d.v with trip := neg32 (blocks p L g d.v) })

/-- The end of a rescale round: another round or the final stage. -/
def roundEnd (d : D) : D :=
  let v := { d.v with trip := addi d.v.trip 1 }
  D.ite (scmpi .ne .b (addi d.v.trip 1) (-1)) (D.mk' (.rbar 0) v) (D.mk' .farr0 v)

/-- The site after the ballot of rescale stage `st`: the stage's first chunk, or its arrivals
when no row of the warp needs rescaling. -/
def afterVote (st : Fin 2) (d : D) (b : BitVec 64) : D :=
  let v := setB d.v b st
  D.ite (scmpi .eq .b b 0) (D.mk' (.rarr st 0) v) (D.mk' (.rld st 0) v)

/-- After the last arrival of the final stage: the LSE stores of the rows the request has
(`%p739`, `%p741`), then the second pass. -/
def afterFinal (p : Params) (L : Launch) (g : Nat) (d : D) : D :=
  let lim := sub32 (sub32 d.v.sc.c1 d.v.sc.c0) (shl (rowOff p L g d.v.sc) 8)
  D.ite (scmp .ge .s (rowW L g) lim)
    (D.ite (scmp .ge .s (rowW L g) (addi lim (-128))) (passStart p L g true d)
      (D.mk' (.lse 1) d.v))
    (D.mk' (.lse 0) d.v)

/-- After LSE store `h`. -/
def afterLse (p : Params) (L : Launch) (g : Nat) (d : D) : Fin 2 → D
  | 0 =>
    let lim := sub32 (sub32 d.v.sc.c1 d.v.sc.c0) (shl (rowOff p L g d.v.sc) 8)
    D.ite (scmp .ge .s (rowW L g) (addi lim (-128))) (passStart p L g true d) (D.mk' (.lse 1) d.v)
  | 1 => passStart p L g true d

/-- The successor after event `e` (at sub-step 0 unless stated). -/
def succ (p : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Option (Option D) :=
  let go (s : Site) : Option (Option D) := some (some (D.mk' s d.v))
  match d.site with
  | .setmax => go .bar1
  | .bar1 => go (.arr 0)
  | .arr 0 => go (.arr 1)
  | .arr 1 => some (some (passStart p L g false d))
  | .word k =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => word32 v fun x => scAt d (.down k) fun c => { c with w := x }
      | .error _ => none
    | _ => none
  | .down k =>
    match e.kind with
    | .shfl _ _ _ _ v _ => word32 v fun x =>
      scAt d (.up k 0) fun c => { c with dn := x, tl := tlOf p L g k c x }
    | _ => none
  | .up k j =>
    match e.kind with
    | .shfl _ _ _ _ v _ => word32 v fun x =>
      match j with
      | 0 => scAt d (.up k 1) fun c => { c with u1 := x }
      | 1 => scAt d (.up k 2) fun c => { c with u2 := x }
      | 2 => scAt d (.up k 3) fun c => { c with u4 := x }
      | 3 => scAt d (.up k 4) fun c => { c with u8 := x }
      | 4 => scAt d (.total k) fun c => { c with u16 := x }
    | _ => none
  | .total k =>
    match e.kind with
    | .shfl _ _ _ _ v _ => word32 v (afterTotal p L g k d)
    | _ => none
  | .vote late =>
    match e.kind with
    | .vote _ _ b =>
      let d := scAt d d.site fun c => { c with bal := BitVec.ofNat 64 b.toNat }
      some (some (D.ite (scmpi .eq .b d.v.sc.bal 0)
        (scAt d (.tiles late) fun c => { c with pv := i32 0 }) (D.mk' (.pre late) d.v)))
    | _ => none
  | .pre late =>
    match e.kind with
    | .shfl _ _ _ _ v _ => word32 v fun x =>
      if late then scAt d (.tiles true) fun c => c
      else scAt d (.tiles false) fun c => { c with pv := mul32 x (headsW p) }
    | _ => none
  | .tiles late =>
    match e.kind with
    | .shfl _ _ _ _ v _ =>
      match v with
      | .bits 32 x =>
        if late then some (some (scAt d (.wend true) fun c => c))
        else (afterTiles p L g d x).map some
      | _ => some none
    | _ => none
  | .q0 =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => word32 v fun x => scAt d .q1 fun c => { c with c0 := x }
      | .error _ => none
    | _ => none
  | .q1 =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => word32 v fun x => scAt d .uk fun c => { c with c1 := x }
      | .error _ => none
    | _ => none
  | .uk =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => word32 v fun x => D.mk' (.nb 0) { d.v with ukw := x }
      | .error _ => none
    | _ => none
  | .nb 0 => go .free
  | .free => go (.nb 1)
  | .nb 1 => some (some (enterRounds p L g d))
  | .rbar st => go (.rscale st)
  | .rscale st =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => scale32 v fun x =>
        D.mk' (.rvote st) (setS d.v x st)
      | .error _ => none
    | _ => none
  | .rvote st =>
    match e.kind with
    | .vote _ _ b => some (some (afterVote st d (BitVec.ofNat 64 b.toNat)))
    | _ => none
  | .rld st c =>
    if d.k = 0 then
      match e.kind with
      | .tc (.ld _ vals _) => match flN 16 vals with
        | some xs => some (some ⟨.rldw st c, { d.v with xs := xs }, 1⟩)
        | none => some none
      | _ => none
    else some none
  | .rldw st c => if d.k = 1 then go (.rst st c) else some none
  | .rst st c => if c.val = 7 then go (.rwait st) else go (.rld st (c + 1))
  | .rwait st => go (.rarr st 0)
  | .rarr st 0 => go (.rarr st 1)
  | .rarr 0 1 => go (.rbar 1)
  | .rarr 1 1 => some (some (roundEnd d))
  | .farr0 => go (.fbar 0)
  | .fbar st => go (.fsum st)
  | .fsum st =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => real32 v fun x =>
        D.mk' (.fmax st) (setRs d.v x st)
      | .error _ => none
    | _ => none
  | .fmax st =>
    match e.kind with
    | .rd _ bs => match rebuild 3 bs with
      | .ok v => max32 v fun x =>
        D.mk' (.farr st) (setRm d.v x st)
      | .error _ => none
    | _ => none
  | .farr st => go (.fw st 0)
  | .fw st k =>
    match e.kind with
    | .wait _ _ ok _ _ =>
      some (some (if ok then D.mk' (if k.val = 0 then .fw st 1 else .fld st 0) d.v else d))
    | _ => none
  | .fld st j =>
    match e.kind with
    | .tc (.ld _ vals _) => match flN 8 vals with
      | some ys => some (some (D.mk' (.fwl st j) { d.v with ys := ys }))
      | none => some none
    | _ => none
  | .fwl st j => go (.fst st j 0)
  | .fst st j h =>
    if d.k.val < 3 then some (some { d with k := d.k + 1 })
    else if h.val = 0 then go (.fst st j 1)
    else if j.val = 15 then go (.fence st) else go (.fld st (j + 1))
  | .fence st => go (.fdone st 0)
  | .fdone st 0 => go (.fdone st 1)
  | .fdone 0 1 => go (.fbar 1)
  | .fdone 1 1 =>
    -- the LSE's logarithms: the kernel's rule on positive row sums, Core's `lg2(+0) = -inf` on
    -- zero ones (the code's `selp` then stores `-inf`); a negative sum is not followed
    if 0 ≤ d.v.rs0 ∧ 0 ≤ d.v.rs1 then some (some (afterFinal p L g d)) else some none
  | .lse 0 => if 0 ≤ d.v.rs1 then some (some (afterLse p L g d 0)) else some none
  | .lse 1 => some (some (afterLse p L g d 1))
  | .wend late =>
    match e.kind with
    | .wait _ _ ok _ _ => some (some (if ok then D.mk' (.barEnd late) d.v else d))
    | _ => none
  | .barEnd late => go (.exit late)
  | .exit _ => none

/-- The midway sub-steps a state may have: the elements of a vector store and the implicit wait
of a rescale load. -/
def Site.midOk : Site → Fin 4 → Prop
  | .fst _ _ _, _ => True
  | .rldw _ _, k => k = 1
  | _, _ => False

/-- The correction warps as a code machine. -/
@[reducible] def Data.code (p : Params) (L : Launch) (g : Nat) :
    Flow.Code kernel Assumptions.all L g where
  D := D
  init := D.mk' .setmax {}
  pc := (·.site.pc)
  facts := facts p L g
  sub := (·.k.val)
  inv := fun d => d.k = 0 ∨ d.site.midOk d.k
  next := succ p L g

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
