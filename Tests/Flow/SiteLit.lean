-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Step.SiteShape
public import Kernels.TmlFa4Fwd.Proof2.Common.Roles

/-! # A site the theorem's hypothesis fixes, and site membership by position

`site_cases`/`site_shape` (`Lemmas/Flow/Step/SiteCases.lean`, `familySites`) substitute a site
variable that a hypothesis of the context fixes by an equation (`hs : s = .tiles false`), so the
theorem's one site is proved directly instead of one goal per constructor of the site type
(tml-fa4's Loader has 566, its Correction 263). Checked here on the correction warp's site type:
the substitution consumes the equation and leaves the site literal, and a membership in the
region's site list is then one position proof (`lit_mem`), not a kernel evaluation of the whole
list (`decide +kernel`).

`site_acc` no longer asks `simp` to decide propositions (`decide := true`): the access's arithmetic
is literal after `site_norm`, and the configuration made `simp` try a `Decidable` instance at every
subterm of every shape goal. -/

namespace PTX.Tests.SiteLit
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof2

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The substitution makes the site literal: its pc is the literal the code's site table has. -/
example (s : Correction.Site) (hs : s = .tiles false) : s.pc ∈ correctionSites := by
  subst hs
  lit_mem

/-- With the site fixed by the hypothesis, its membership is a position proof: `lit_mem` walks to
the entry's position and compares no numbers, while `decide +kernel` evaluates the whole 263-entry
list for every site goal. -/
example (s : Correction.Site) (hs : s = .tiles false) : s.pc ∈ correctionSites := by
  subst hs
  lit_mem

/-- Without an equation on the site variable nothing is substituted. -/
example (s : Correction.Site) (h : s.pc ∈ correctionSites) :
    s.pc ∈ correctionSites := h

/-- A membership of a literal pc in the loader region's list, by position. -/
example : (179 : Nat) ∈ loaderSites := by lit_mem

/-- The startup warp's sites are a short list: `lit_mem` proves each by position. -/
example (s : Startup.Site) : s.pc ∈ startupSites := by
  cases s with
  | sh j => fin_cases j <;> lit_mem
  | elect j => fin_cases j <;> lit_mem
  | init n => fin_cases n <;> lit_mem
  | enter r => cases r <;> lit_mem
  | _ => lit_mem

end PTX.Tests.SiteLit
