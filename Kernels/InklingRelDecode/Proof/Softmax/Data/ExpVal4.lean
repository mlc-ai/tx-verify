-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.ExpVal3
public import Kernels.InklingRelDecode.Proof.Softmax.Data.PkKinds

@[expose] public section

/-! # The exponent window's words, the row sum and the probability words

Register `1994 + k` holds the exponentials of the shifted scores `X (1288 + 32 (k / 6) + 4 (k % 6))`
and the next register of the shifted scores as a pair, register `508 + i` the exponential of the
input of software instance `i`. The pack turns word `c` of the store into the `bf16` pair of the
exponentials of `X (1288 + 4 c)` and `X (1290 + 4 c)`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
noncomputable section

/-- The pair register `k`: two adjacent exponentials. -/
def pairTab (X : Nat → EReal) (k : Nat) : Value :=
  joinValue (.float .f32 (pw2 (X (1288 + 32 * (k / 6) + 4 * (k % 6)))))
    (.float .f32 (pw2 (X (1290 + 32 * (k / 6) + 4 * (k % 6)))))

/-- The single register `i`: the exponential of the input of software instance `i`. -/
def singTab (X : Nat → EReal) (i : Nat) : Value := .float .f32 (pw2 (X (swTab i)))

/-- **The exponent window's words** (registers 1994 to 2017, 508 to 523) and **the row sum**
(register 1529), from the shifted scores `X` and the outputs of the software instances. -/
theorem e2_regs {W : Nat → Value} {X : Nat → EReal} (hx : ∀ r ∈ xRegs, Ev (W r) (X r))
    (hy : ∀ r, 1271 ≤ r → r < 1287 → W r = .float .f32 (pw2 (X (swTab (r - 1271)))))
    {q q' : Bool} (hq : W 179 = .pred q) (hq' : W 180 = .pred q') :
    ∀ p ∈ Gen.ex2_facts5 W, (1994 ≤ p.1 → p.1 < 2018 → p.2 = pairTab X (p.1 - 1994)) ∧
      (508 ≤ p.1 → p.1 < 524 → p.2 = singTab X (p.1 - 508)) ∧
      (1529 = p.1 → p.2 = .float .f32 ((xRegs.map fun r => pw2 (X r)).sum)) := by
  intro p hp
  simp only [Gen.ex2_facts5, List.mem_cons, List.not_mem_nil] at hp
  repeat' rcases hp with rfl | hp
  all_goals
    refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 => ?_⟩ <;> try (exfalso; omega)
    all_goals
      simp (disch := first | decide | decide +kernel) only [
        Gen.ex2_v2089, Gen.ex2_v2090, Gen.ex2_v2091, Gen.ex2_v2092, Gen.ex2_v2093,
        Gen.ex2_v2094, Gen.ex2_v2095, Gen.ex2_v2096, Gen.ex2_v2097, Gen.ex2_v2098,
        Gen.ex2_v2099, Gen.ex2_v2100, Gen.ex2_v2101, Gen.ex2_v2102, Gen.ex2_v2103,
        Gen.ex2_v2104, Gen.ex2_v2105, Gen.ex2_v2106, Gen.ex2_v2107, Gen.ex2_v2108,
        Gen.ex2_v2109, Gen.ex2_v2110, Gen.ex2_v2111, Gen.ex2_v2112, Gen.ex2_v2113,
        Gen.ex2_v2114, Gen.ex2_v2115, Gen.ex2_v2116, Gen.ex2_v2117, Gen.ex2_v2118,
        Gen.ex2_v2119, Gen.ex2_v2120, Gen.ex2_v2121, Gen.ex2_v2122, Gen.ex2_v2123,
        Gen.ex2_v2124, Gen.ex2_v2125, Gen.ex2_v2126, Gen.ex2_v2127, Gen.ex2_v2128,
        Gen.ex2_v2129, Gen.ex2_v2130, Gen.ex2_v2131, Gen.ex2_v2132, Gen.ex2_v2133,
        Gen.ex2_v2134, Gen.ex2_v2135, Gen.ex2_v2136, Gen.ex2_v2137, Gen.ex2_v2138,
        Gen.ex2_v2139, Gen.ex2_v2140, Gen.ex2_v2141, Gen.ex2_v2142, Gen.ex2_v2143,
        Gen.ex2_v2144, Gen.ex2_v2145, Gen.ex2_v2146, Gen.ex2_v2147, Gen.ex2_v2148,
        Gen.ex2_v2149, Gen.ex2_v2150, Gen.ex2_v2151, Gen.ex2_v2152, Gen.ex2_v2153,
        Gen.ex2_v2154, Gen.ex2_v2155, Gen.ex2_v2156, Gen.ex2_v2157, Gen.ex2_v2158,
        Gen.ex2_v2159, Gen.ex2_v2160, Gen.ex2_v2161, Gen.ex2_v2162, Gen.ex2_v2163,
        Gen.ex2_v2164, Gen.ex2_v2165, Gen.ex2_v2166, Gen.ex2_v2167, Gen.ex2_v2168,
        Gen.ex2_v2169, Gen.ex2_v2170, Gen.ex2_v2171, Gen.ex2_v2172, Gen.ex2_v2173,
        Gen.ex2_v2174, Gen.ex2_v2175, Gen.ex2_v2176, Gen.ex2_v2177, Gen.ex2_v2178,
        Gen.ex2_v2179, Gen.ex2_v2180, Gen.ex2_v2181, Gen.ex2_v2182, Gen.ex2_v2183,
        Gen.ex2_v2184, Gen.ex2_v2185, Gen.ex2_v2186, Gen.ex2_v2187, Gen.ex2_v2188,
        Gen.ex2_v2189, Gen.ex2_v2190, Gen.ex2_v2191, Gen.ex2_v2192, Gen.ex2_v2193,
        Gen.ex2_v2194, Gen.ex2_v2195, Gen.ex2_v2196, Gen.ex2_v2197, Gen.ex2_v2198,
        Gen.ex2_v2199, Gen.ex2_v2200, Gen.ex2_v2201, Gen.ex2_v2202, Gen.ex2_v2203,
        Gen.ex2_v2204, Gen.ex2_v2205, Gen.ex2_v2206, Gen.ex2_v2207, Gen.ex2_v2208,
        Gen.ex2_v2209, Gen.ex2_v2210, Gen.ex2_v2211, Gen.ex2_v2212, Gen.ex2_v2213,
        Gen.ex2_v2214, Gen.ex2_v2215, Gen.ex2_v2216, Gen.ex2_v2217, Gen.ex2_v2218,
        Gen.ex2_v2219, Gen.ex2_v2220, Gen.ex2_v2221, Gen.ex2_v2222, Gen.ex2_v2223,
        Gen.ex2_v2224, Gen.ex2_v2225, Gen.ex2_v2226, Gen.ex2_v2227, Gen.ex2_v2228,
        Gen.ex2_v2229, Gen.ex2_v2230, Gen.ex2_v2231, Gen.ex2_v2232_0, Gen.ex2_v2232_1,
        Gen.ex2_v2233, Gen.ex2_op2153, Gen.ex2_op2154, Gen.ex2_op2155, Gen.ex2_op2156,
        Gen.ex2_op2157, Gen.ex2_op2158, Gen.ex2_op2159, Gen.ex2_op2160, Gen.ex2_op2161,
        Gen.ex2_op2162, Gen.ex2_op2163, Gen.ex2_op2164, Gen.ex2_op2165, Gen.ex2_op2166,
        Gen.ex2_op2167, Gen.ex2_op2168, ex2_val hx, hy, hq, hq', add2F, selp_float, addF,
        split_pair, pairTab, singTab, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv,
        Nat.reduceMod, Nat.reduceSub, swTab, List.getD_cons_zero, List.getD_cons_succ]
    all_goals
      rw [xRegs_eq]
      simp only [List.range_succ, List.map_cons, List.sum_cons, List.sum_nil, List.map_nil,
        List.range_zero, List.map_append, List.sum_append, List.nil_append]
      congr 1
      ring_nf

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
