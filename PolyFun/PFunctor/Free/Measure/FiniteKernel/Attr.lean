/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.PFunctor.Free.Measure.StatefulExpectedCharge

/-!
# Computing finite expected charges

The `expected_cost` simp set reads the syntax of finite programs, then computes integrals
against explicit atomic measures. An opaque kernel leaves the continuation integral visible.
-/

public section

/-- Constructor and atomic-measure equations for finite expected-cost calculations. -/
register_simp_attr expected_cost
