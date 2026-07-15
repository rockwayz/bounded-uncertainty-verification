/-
  VCalc.Basic — a four-state verification-output calculus (PHASE 1: TYPE LAYER)
  ============================================================================

  Thesis this formalization serves.
  --------------------------------
  A binary "safe / unsafe" verdict on an AI system is dishonest: Rice's theorem,
  generalized to abstract semantics by Baldan–Ranzato–Zhang (2021), shows every
  non-trivial semantic property is undecidable, and every decidable
  over-approximation of it admits infinitely many false positives. Honest
  assurance therefore reports an EPISTEMIC STATUS alongside any verdict. This
  module fixes the TYPES that carry that status so that dishonest states are
  literally unrepresentable.

  Scope of THIS file (Phase 1).
  -----------------------------
  Types only:
    * `State`         — the four epistemic states (a flat enum; SKIPPED is NOT here).
    * `Skipped`       — the *separate* non-evaluation annotation.
    * `RiskParams`    — per-mechanism residual risk (ε, δ) over mathlib `ℝ`.
    * `Certificate`   — scope + state + risk ledger, with the structural invariant
                        that residual risk exists IFF the state is APPROXIMATION.
    * `Budget`        — the global privacy-accountant record (its own append-only
                        spend ledger + the DRV slack δ').
    * `ReportEntry`   — `Certificate ⊕ Skipped`: assurance XOR a skip.
  Plus a handful of pure projections (`rank`, `assuranceContent`) and the atomic
  smart constructors, which only *characterize* / *inhabit* the types.

  Deliberately NOT in this file (later phases, so the types must merely make them
  provable):
    * `compose` and its associativity                          — Phase 2 / Theorem 1
    * exhaustive + mutually-exclusive states                   — Phase 3 / Theorem 2
    * budget monotonicity                                       — Phase 3 / Theorem 3
    * exhaustion soundness                                      — Phase 3 / Theorem 4
    * the DRV accounting function `drvEps` / exhaustion check   — Phase 2 (query-time)

  The single most load-bearing design decision — WHY residual risk is a LEDGER
  (a `List RiskParams`) rather than a baked-in (ε,δ) pair — is documented at
  `RiskParams` / `Certificate` below. Read that comment first.
-/

import Mathlib.Data.Real.Basic          -- ℝ
import Mathlib.Data.Set.Basic           -- Set Ω  (the scope a certificate is relative to)
import Mathlib.Data.List.Basic          -- List   (the risk ledger)
import Mathlib.Tactic.DeriveFintype     -- `deriving Fintype` for the four-state enum
-- Phase-2 imports (the DRV accountant, §9): sqrt / log / exp over ℝ.
-- NOTE: `Mathlib.Data.Real.Sqrt` is deprecated; `Mathlib.Analysis.Real.Sqrt` is current.
import Mathlib.Analysis.Real.Sqrt                   -- Real.sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic  -- Real.log
import Mathlib.Analysis.SpecialFunctions.Exp        -- Real.exp

namespace VCalc

universe u

/-! ## 1. The four epistemic states

`State` has EXACTLY four nullary constructors and no payload. Keeping it flat (rather
than carrying `(ε,δ)` inside the APPROXIMATION constructor) is what lets Phase-3
Theorem 2 — "the four states are exhaustive and mutually exclusive" — be a statement
about the constructors *themselves* (a two-line `decide`), with no auxiliary tag
projection. `Fintype` is derived so that `Fintype.card State = 4` is available to that
theorem.

SKIPPED is deliberately ABSENT: non-evaluation must never be representable as an
assurance state. It lives in its own type (`Skipped`, §3). -/
inductive State where
  | PROVEN
  | APPROXIMATION
  | ESCALATED
  | TERMINATED
  deriving DecidableEq, Repr, Fintype

namespace State

/-- Epistemic rank = "how much assurance may still be recovered", used to order the
states linearly for weakest-member composition (Phase 2's `meet` = min by `rank`).

    TERMINATED (0) < ESCALATED (1) < APPROXIMATION (2) < PROVEN (3)

WHY LINEAR (and why this is forced, not chosen): weakest-member composition is an
associative, idempotent operation closed on these four states, i.e. a meet on a
4-element order with PROVEN > APPROXIMATION > {ESCALATED, TERMINATED}. If ESCALATED and
TERMINATED were incomparable, their meet would need a common lower bound below both —
which does not exist without inventing a fifth ⊥ state, and the spec forbids a fifth
state. So a total order is the only way to keep four states AND an associative
weakest-member meet.

WHY this DIRECTION (ESCALATED above TERMINATED): ESCALATED routes to a human / further
analysis — a live path along which a stronger verdict may yet be recovered. TERMINATED
is a halt / refusal with no remaining path. So ESCALATED retains strictly more
recoverable assurance than TERMINATED. Both sit strictly below APPROXIMATION, satisfying
the constraint that budget exhaustion yields "TERMINATED or ESCALATED, never a diluted
APPROXIMATION". -/
def rank : State → ℕ
  | .PROVEN        => 3
  | .APPROXIMATION => 2
  | .ESCALATED     => 1
  | .TERMINATED    => 0

/-- Assurance content = "how much guarantee is actually claimed", a *separate* axis from
`rank`. ESCALATED and TERMINATED are ordered by `rank` (recourse) but tie here at 0
(neither issues any guarantee). Phase 3 will prove `meet` never inflates this, so the
linear `rank` order commits only to a recovery/disposition ordering and never overstates
assurance — the honest reading of a linearization that ranks ESCALATED above TERMINATED. -/
def assuranceContent : State → ℕ
  | .PROVEN        => 2
  | .APPROXIMATION => 1
  | .ESCALATED     => 0
  | .TERMINATED    => 0

end State

/-! ## 2. Residual risk, and the ledger resolution of the DRV / associativity tension

Each APPROXIMATION mechanism carries residual-risk parameters `(ε, δ)` — a bound of the
form "the reported property holds except with (ε,δ)-differential-privacy-style slack".

THE CENTRAL DESIGN DECISION — WHY A LEDGER, NOT A BAKED-IN (ε,δ) PAIR.
The paper cites Dwork–Rothblum–Vadhan (FOCS 2010) advanced composition: k mechanisms
each (ε,δ) compose to

    ε_g = sqrt(2k · ln(1/δ')) · ε + k · ε · (e^ε − 1),   δ_total = k·δ + δ'.

The leading term grows as sqrt(k), NOT k — that sub-linear growth is the entire reason
the paper invokes DRV. Baking this bound into a BINARY composition operator is fatal on
two independently verified counts:
  (1) ILL-TYPED: the formula is HOMOGENEOUS ("k mechanisms EACH (ε,δ)", one shared ε);
      two certificates with different ε have no shared ε to substitute.
  (2) NON-ASSOCIATIVE AND SELF-DEFEATING: iterating a binary DRV bound reintroduces
      linear-or-worse growth. Measured at ε=0.1, δ=δ'=1e-6: one-shot k=3 gives
      ε_g = 0.942, but folding a binary bound (2 then 2) gives 7.437 — 7.9× worse. That
      destroys the sqrt(k) advantage the bound exists to provide.

RESOLUTION (the real differential-privacy accountant pattern): residual risk is an
APPEND-ONLY LEDGER of per-mechanism `RiskParams`. Composition (Phase 2) will *append*
ledgers — append is associative by construction (`List.append_assoc`), does no DRV
arithmetic, and so can never reintroduce the 7.9× blow-up. The DRV bound becomes an
ACCOUNTING FUNCTION evaluated ONCE over the whole ledger at query time (k = ledger
length), which recovers the honest one-shot 0.942 and never the iterated 7.437. That
accounting function is Phase 2; here we only fix the ledger type it consumes.

THE HOMOGENEITY TRAP, and the soundness boundary the paper must state. DRV needs one
shared ε, but a heterogeneous ledger holds many. The Phase-2 accountant will evaluate at
`ε_max`. That is a SOUND UPPER BOUND *only as a modeling assumption* resting on
DP's monotonicity in ε (an ε_i-DP mechanism is also ε_max-DP) — which is CITED, not
formalized here (a Lean proof would need DP measure semantics, out of scope). What Phase
3 will actually prove is only that the accountant is monotone in ε and in k. A fully
sound alternative — a homogeneous-ledger theorem with an `all ε equal` hypothesis and no
DP assumption — should ship alongside it. This file commits to neither policy; it only
provides the `List RiskParams` both consume.

Side conditions carried AS FIELDS (so an ill-formed mechanism is unconstructible): ε ≥ 0
and δ ≥ 0. The ε ≥ 0 field is what makes `e^ε − 1 ≥ 0`, needed later for budget
monotonicity. (ε ≥ 0 rather than ε > 0 is a deliberate generality choice; see the
forced-decision note returned with this file.) -/
structure RiskParams where
  eps         : ℝ
  delta       : ℝ
  eps_nonneg  : 0 ≤ eps
  delta_nonneg : 0 ≤ delta

/-! ## 3. SKIPPED — a *separate* non-evaluation annotation

`Skipped` records that a specification was NOT evaluated on some region. It is a distinct
type from `Certificate`: it has NO `state` field (so it cannot even be asked for a
verdict) and there is NO function `Skipped → Certificate`. Structurally, therefore,
non-evaluation can never be laundered into any assurance state — enforced by the absence
of an injection, not by convention.

A report is a `Certificate ⊕ Skipped` (§5): a skip is only ever `Sum.inr`, disjoint from
every certificate `Sum.inl`, so any total function aggregating a report must pattern-match
the skip branch and cannot silently score it as PROVEN. `scope` is retained purely for
audit ("what was skipped"); it grants no assurance. -/
structure Skipped (Ω : Type u) where
  scope  : Set Ω
  reason : String

/-! ## 4. The Certificate

A certificate bundles:
  * `scope`  : the specification it is relative to, as `Set Ω` for a carrier `Ω`.
               Composition (Phase 2) intersects scopes; `∩` is associative
               unconditionally (`Set.inter_assoc`), so scope never obstructs
               associativity. An empty intersection yields a vacuously-true
               PROVEN-on-∅ certificate — sound (it licenses no concrete input, since
               `ω ∈ ∅` is always false) though degenerate; this file does not block it.
  * `state`  : one of the four epistemic states.
  * `ledger` : the append-only residual-risk ledger (§2).
  * `ledger_iff` : the STRUCTURAL INVARIANT making illegal states unrepresentable —
               the ledger is non-empty IFF the state is APPROXIMATION.

WHY THE INVARIANT IS A STORED FIELD. The spec requires "for APPROXIMATION only:
residual-risk parameters" and "illegal states UNREPRESENTABLE". Carrying the invariant as
a field makes that literal: one cannot construct a non-APPROXIMATION certificate that
carries risk, nor an APPROXIMATION certificate that carries none — the offending term does
not typecheck because its `ledger_iff` proof cannot be supplied. This is strictly stronger
than a derived "present risk only if APPROXIMATION" projection, which would leave a
PROVEN-carrying-a-ledger term *representable* (merely un-presented).

The known cost (recorded in the forced-decision note): in Phase 2, `compose` must MAINTAIN
this invariant, which forces conditional clearing of the *claim* ledger when the composed
state falls below APPROXIMATION. That is sound — the composite makes no residual-risk
claim, and the actual SPEND is recorded separately in the global `Budget` ledger (§5), not
in this per-certificate claim ledger — and it is provably associative, by state case
analysis plus this very invariant: in the one asymmetric case (an inner pair meeting at
PROVEN inside a triple meeting at APPROXIMATION) both inner members are PROVEN, so their
ledgers are already `[]` and clearing versus appending coincide (see §12, Law 1). The alternative
(append-only per-cert ledger + derived projection) never clears and so never drops a
claim, at the price of leaving illegal states representable; that trade is flagged for the
user. -/
-- `@[ext]` is the ONE sanctioned Phase-2 touch to a Phase-1 declaration: it generates
-- `Certificate.ext` (two certificates agreeing on `scope`, `state`, `ledger` are equal —
-- the `ledger_iff` proof field is irrelevant by proof irrelevance), which Phase 3's
-- extensionality-based theorems (associativity of `compose`, in particular) consume.
@[ext]
structure Certificate (Ω : Type u) where
  scope     : Set Ω
  state     : State
  ledger    : List RiskParams
  /-- Residual risk exists exactly when the state is APPROXIMATION. -/
  ledger_iff : ledger ≠ [] ↔ state = State.APPROXIMATION

namespace Certificate

/-! ### Atomic smart constructors

These build a single certificate in each state with its invariant discharged (trivially).
They are NOT composition — they take no certificate as input — and exist to (a) witness
that the invariant is satisfiable in every state, i.e. `Certificate` is inhabited across
all four constructors, and (b) give downstream code the only sanctioned way to mint an
atomic certificate. The DRV accountant and budget-gated issuance are Phase 2. -/

/-- A fully proven certificate over `scope`: no residual risk. -/
def proven (scope : Set Ω) : Certificate Ω :=
  { scope := scope, state := .PROVEN, ledger := []
    ledger_iff := iff_of_false (by simp) (by decide) }

/-- A single-mechanism approximation over `scope`, carrying its `(ε,δ)` risk. -/
def approx (scope : Set Ω) (r : RiskParams) : Certificate Ω :=
  { scope := scope, state := .APPROXIMATION, ledger := [r]
    ledger_iff := iff_of_true (by simp) rfl }

/-- An escalated certificate (handed to a human / further analysis): no risk claim. -/
def escalated (scope : Set Ω) : Certificate Ω :=
  { scope := scope, state := .ESCALATED, ledger := []
    ledger_iff := iff_of_false (by simp) (by decide) }

/-- A terminated certificate (halted / refused): no risk claim. -/
def terminated (scope : Set Ω) : Certificate Ω :=
  { scope := scope, state := .TERMINATED, ledger := []
    ledger_iff := iff_of_false (by simp) (by decide) }

end Certificate

/-! ## 5. Report entries — assurance XOR a skip

A report entry is a sum: either a genuine `Certificate` (`Sum.inl`) or a `Skipped`
annotation (`Sum.inr`). Because the two are disjoint constructors of a sum and there is no
injection `Skipped → Certificate`, non-evaluation can never appear where assurance is
expected. (The disjointness fact `Sum.inl c ≠ Sum.inr s` is definitional; the aggregation
theorems that rely on it are Phase 3.) -/
abbrev ReportEntry (Ω : Type u) := Certificate Ω ⊕ Skipped Ω

/-! ## 6. The Budget — the global privacy accountant

The Budget is the authoritative SPEND record, kept separate from any certificate's CLAIM
ledger (§4). This separation is what keeps conditional clearing of a claim ledger
leak-free: when a composite drops below APPROXIMATION and its claim ledger is cleared, the
spend it represented was already committed here.

Fields:
  * `epsCeiling`, `deltaCeiling` : the caps the accounted (ε,δ) must not exceed. Two
        dimensions because DRV produces both a composed ε and a total δ.
  * `spent` : the global APPEND-ONLY ledger of every mechanism ever charged. It is a full
        `List RiskParams`, not a scalar, precisely because advanced composition is NOT
        additive — the Phase-2 exhaustion check must re-apply DRV over the whole list
        (k = `spent.length`, ε at `ε_max`), so the per-mechanism detail must be retained.
  * `deltaPrime` (δ') : the DRV free-slack parameter. It is the ACCOUNTANT's global choice,
        NOT a property of any mechanism, so it lives here and not on `RiskParams`.

Side conditions on δ', carried AS FIELDS so a junk budget is unconstructible:
    `dp_pos : 0 < δ'`  and  `dp_le1 : δ' ≤ 1`.
`ln(1/δ') ≥ 0` (needed for the DRV bound to be non-negative and monotone) requires exactly
`δ' ∈ (0, 1]`; making these fields means every Budget that typechecks already carries the
witnesses the Phase-3 monotonicity / non-negativity proofs consume. -/
structure Budget where
  epsCeiling   : ℝ
  deltaCeiling : ℝ
  spent        : List RiskParams
  deltaPrime   : ℝ
  dp_pos       : 0 < deltaPrime
  dp_le1       : deltaPrime ≤ 1

/-!
============================================================================
  PHASE 2 — THE COMPOSITION OPERATION AND ITS SUPPORTING DEFINITIONS
============================================================================

Everything below is Phase 2: `meet`, `compose`, the DRV accountant, budget
operations, and budget-gated issuance. Definitions carry exactly the inline
proof obligations they need to typecheck (e.g. discharging `ledger_iff`
inside `compose`); the four composition-law THEOREMS are Phase 3 and are
deliberately absent (see §12).
-/

/-! ## 7. Weakest-member meet on states

`meet` picks the member of `{a, b}` with the smaller `rank` — the WEAKEST of the two
verdicts, per the linear order justified at `State.rank` (§1). It is a bare `def`, not a
`Min`/`LinearOrder` instance: Phase 3 discharges its algebraic laws (associativity,
idempotence, ...) by `decide` over the 4-element enum, and a bare def keeps those goals
free of instance-unfolding noise. -/

namespace State

/-- Weakest member of two states: min by `rank`. Ties are impossible across distinct
states (`rank` is injective on the four constructors), and on equal states either branch
returns the same value, so the `≤` tie-break is inert. -/
def meet (a b : State) : State :=
  if a.rank ≤ b.rank then a else b

/-- `meet` SELECTS one of its two arguments — it never invents a state. This is the
load-bearing fact for `compose`'s inline `ledger_iff` discharge (§8): if the meet is
APPROXIMATION then one of the two input certificates IS an APPROXIMATION. -/
theorem meet_eq_left_or_right (a b : State) : a.meet b = a ∨ a.meet b = b := by
  unfold meet
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

end State

/-! ## 8. Composition of certificates

`compose` is TOTAL on scopes (user ruling R5): an empty intersection is permitted and
yields a vacuously-true PROVEN-on-∅ composite when both inputs are PROVEN — sound, since
a certificate over ∅ licenses no concrete input.

CONDITIONAL CLEARING OF THE CLAIM LEDGER (user ruling R1 — the WHY). `Certificate` keeps
the stored `ledger_iff` invariant, so a composite whose state falls below APPROXIMATION
*cannot* carry a non-empty ledger — the term would not typecheck. Clearing is honest
because the per-certificate ledger is a CLAIM ledger ("this much residual risk backs THIS
assurance"): a composite in state ESCALATED or TERMINATED makes no residual-risk claim,
so it carries none. Nothing is lost by clearing — the authoritative SPEND record lives in
the separate global `Budget.spent` ledger (§6), which `compose` NEVER touches (note the
type: no `Budget` anywhere). When the meet IS APPROXIMATION, the ledgers are APPENDED —
no DRV arithmetic happens here, which is exactly what preserves associativity and the
sqrt(k) advantage (§2); the DRV bound is applied once, at query time, by the §9
accountant. -/

namespace Certificate

/-- Supporting lemma about the TYPE (not a Phase-3 theorem): a certificate whose state is
not APPROXIMATION carries an empty ledger. Direct consequence of the stored `ledger_iff`. -/
theorem ledger_eq_nil_of_ne (c : Certificate Ω) (h : c.state ≠ State.APPROXIMATION) :
    c.ledger = [] := by
  by_contra hne
  exact h (c.ledger_iff.mp hne)

/-- Supporting lemma, the other direction: an APPROXIMATION certificate's ledger is
non-empty. -/
theorem ledger_ne_nil_of_approx (c : Certificate Ω) (h : c.state = State.APPROXIMATION) :
    c.ledger ≠ [] :=
  c.ledger_iff.mpr h

/-- Composition: intersect scopes, take the weakest state, and append the claim ledgers
iff the composed state is APPROXIMATION (else clear — see the section comment for why
clearing is sound and where spend actually lives).

The inline `ledger_iff` discharge is Phase-2 typechecking work, not a Phase-3 theorem:
if the meet is APPROXIMATION then by `State.meet_eq_left_or_right` one of the two inputs
IS an APPROXIMATION, its `ledger_iff` gives a non-empty ledger, and an append with a
non-empty operand is non-empty. -/
def compose (c d : Certificate Ω) : Certificate Ω where
  scope  := c.scope ∩ d.scope
  state  := c.state.meet d.state
  ledger := if c.state.meet d.state = State.APPROXIMATION then c.ledger ++ d.ledger else []
  ledger_iff := by
    split_ifs with h
    · -- Composed state IS APPROXIMATION: both sides of the iff are true.
      refine iff_of_true ?_ h
      rcases State.meet_eq_left_or_right c.state d.state with hm | hm
      · have hc : c.ledger ≠ [] := c.ledger_ne_nil_of_approx (hm.symm.trans h)
        intro hnil
        exact hc (List.append_eq_nil_iff.mp hnil).1
      · have hd : d.ledger ≠ [] := d.ledger_ne_nil_of_approx (hm.symm.trans h)
        intro hnil
        exact hd (List.append_eq_nil_iff.mp hnil).2
    · -- Composed state is NOT APPROXIMATION: both sides are false (ledger cleared to []).
      exact iff_of_false (by simp) h

end Certificate

/-- Scoped infix for `Certificate.compose`. Deliberately NOT a `Mul` instance — `*` would
smuggle in monoid expectations (a unit, in particular) that the calculus does not offer. -/
scoped infixl:65 " ∘ᶜ " => Certificate.compose

/-! ## 9. The DRV accountant (query-time, over a whole ledger)

The Dwork–Rothblum–Vadhan advanced-composition bound, evaluated ONCE over an entire
ledger — NEVER inside `compose`. `k` is the FULL ledger length at evaluation time; this
one-shot evaluation is precisely what preserves the sqrt(k) leading term (iterating a
binary DRV bound reintroduces linear-or-worse growth — the measured 7.9× blow-up
documented in §2). Likewise δ' is applied ONCE here, by the accountant, never
per-composition — charging δ' at every binary step would accumulate k·δ' of slack that
the one-shot bound does not spend.

HETEROGENEITY (user ruling R3): DRV is stated for k mechanisms EACH (ε,δ) — one shared ε.
A real ledger is heterogeneous, so the accountant evaluates the bound at the worst-case
`ε_max` over the ledger. This is a sound upper bound ONLY as a modeling assumption
resting on DP's monotonicity in ε (an ε_i-DP mechanism is also ε_max-DP for ε_i ≤ ε_max)
— CITED, NOT FORMALIZED here (a Lean proof would need DP measure semantics, out of
scope). An exact homogeneous-ledger lemma (all-ε-equal hypothesis, no DP assumption)
ships in Phase 3.

`noncomputable`: only where genuinely forced — `Real.sqrt`, `Real.log`, `Real.exp` have
no executable code in mathlib, so `drvEps` and `spentEps` are noncomputable (as is `issue`
in §11, which branches classically on an undecidable ℝ-comparison). `ledgerEpsMax` and
`spentDelta` use only `max`/`+`/`sum` on ℝ, which compile, so they stay plain `def`s.
Either way this file is a FORMALIZATION of the accountant, not a runtime — a runtime
would evaluate over rationals or floats against these definitions. -/

/-- The DRV advanced-composition ε-bound for `k` mechanisms, each ε-DP, with free slack
`dp` (= δ'):  `sqrt(2k·ln(1/δ'))·ε + k·ε·(e^ε − 1)`. -/
noncomputable def drvEps (k : ℕ) (eps dp : ℝ) : ℝ :=
  Real.sqrt (2 * (k : ℝ) * Real.log (1 / dp)) * eps + (k : ℝ) * eps * (Real.exp eps - 1)

/-- Worst-case ε over a ledger: fold of `max` over the `eps` fields, base 0. Base 0 is
sound because every stored ε is ≥ 0 (`RiskParams.eps_nonneg`), so the base never exceeds
a genuine entry; on the empty ledger it makes `drvEps _ 0 _ = 0` — no spend. -/
def ledgerEpsMax (l : List RiskParams) : ℝ :=
  l.foldr (fun r m => max r.eps m) 0

/-- Accounted ε-spend of a budget: the one-shot DRV bound over the WHOLE spend ledger
(k = length, ε at worst case). -/
noncomputable def spentEps (B : Budget) : ℝ :=
  drvEps B.spent.length (ledgerEpsMax B.spent) B.deltaPrime

/-- Accounted δ-spend of a budget: `Σ δ_i + δ'`. Per DRV, δ composes ADDITIVELY (no
sqrt-savings on the δ axis), and δ' is added exactly once, here. -/
def spentDelta (B : Budget) : ℝ :=
  (B.spent.map (·.delta)).sum + B.deltaPrime

/-! ## 10. Budget operations -/

namespace Budget

/-- Charge one mechanism to the budget: APPEND to the global spend ledger. Ceilings and
δ' are untouched — a charge never moves the goalposts. Appended at the tail so the ledger
reads in spend order (any order gives the same accountant value; `drvEps` sees only
length and max). -/
def charge (B : Budget) (r : RiskParams) : Budget :=
  { B with spent := B.spent ++ [r] }

/-- Budget exhaustion: the accounted spend exceeds a ceiling on EITHER axis.

WHY `Prop`, NOT `Bool`: the comparison is between real numbers, which is undecidable —
there is no `Bool`-valued exhaustion check on mathlib's ℝ. Issuance (§11) therefore
branches by `Classical` choice and is noncomputable: again, this is a formalization of
the accountant's specification, not a runtime. -/
def exhausted (B : Budget) : Prop :=
  B.epsCeiling < spentEps B ∨ B.deltaCeiling < spentDelta B

end Budget

/-! ## 11. Budget-gated issuance — the ONLY sanctioned mint of an APPROXIMATION

`Certificate.approx` (§4) can inhabit the type, but the CALCULUS mints an APPROXIMATION
only through `issue`, which consults the accountant first. (No conflict with §4's
"sanctioned" language: `approx` remains the sanctioned TYPE-LEVEL constructor; `issue` is
the sanctioned ACCOUNTING-LEVEL operation and is `approx`'s only budget-consulting caller.
Accordingly, Phase 3's exhaustion soundness is a theorem about `issue`'s OUTPUT — not the
false stronger claim that no APPROXIMATION term can exist without a budget.) -/

/-- Caller-chosen disposition when the budget refuses an issuance (user ruling R4).

A dedicated two-constructor enum — NOT a `State` — so that PROVEN or APPROXIMATION can
never be smuggled through the fallback path: the offending constructor simply does not
exist here. `TERMINATED` is the documented DEFAULT disposition (witnessed by the
`Inhabited` instance); callers with a live recovery path opt into `ESCALATED`. -/
inductive Fallback where
  | ESCALATED
  | TERMINATED
  deriving DecidableEq, Repr

/-- The documented default fallback disposition is TERMINATED. -/
instance : Inhabited Fallback := ⟨.TERMINATED⟩

/-- Realize a fallback as its (risk-free) certificate over `scope`. By construction the
image is contained in `{ESCALATED, TERMINATED}` certificates. -/
def Fallback.certificate (fb : Fallback) (scope : Set Ω) : Certificate Ω :=
  match fb with
  | .ESCALATED  => Certificate.escalated scope
  | .TERMINATED => Certificate.terminated scope

open Classical in
/-- Budget-gated issuance of an APPROXIMATION certificate.

GATE SEMANTICS (deliberate): the gate tests the POST-charge accountant value —
`¬ (B.charge r).exhausted` — so a query whose admission would breach a ceiling is refused
BEFORE any dilution occurs. This is the "never a diluted APPROXIMATION" clause: an
APPROXIMATION is only ever minted with its full charge already inside the ceilings.
On refusal the ORIGINAL budget is returned — a refusal draws no budget (the mechanism
never ran under the refused charge, so there is no spend to record).

Phase 3's exhaustion soundness will additionally need charge-monotonicity
(`exhausted B → exhausted (B.charge r)`) to conclude that an exhausted budget can never
mint again; that theorem is Phase 3's job, not stated here.

`noncomputable` and `Classical`: `exhausted` is a `Prop` over ℝ (see §10), so the branch
is by classical choice — a specification of the gate, not executable code. -/
noncomputable def issue (B : Budget) (scope : Set Ω) (r : RiskParams) (fb : Fallback) :
    Certificate Ω × Budget :=
  if ¬ (B.charge r).exhausted then
    (Certificate.approx scope r, B.charge r)   -- within ceilings: mint AND commit spend
  else
    (fb.certificate scope, B)                  -- refusal: fallback cert, budget untouched

/-! ## 12. Law-witnessing remarks — where Phase 3 discharges the four composition laws

COMMENTS ONLY; no theorem statements below (Phase-3 scope boundary).

  LAW 1 — ASSOCIATIVITY of `compose` (Phase 3, Theorem 1).
    Componentwise via `Certificate.ext` (the §4 `@[ext]` attribute):
    scope: `Set.inter_assoc`; state: associativity of `State.meet` by `decide` over the
    4-element enum; ledger: the outer clearing guards agree because the state meet is
    associative, and on the kept branch `List.append_assoc` applies — PLUS, in the mixed
    associations where an INNER pair meets at PROVEN inside a triple that meets at
    APPROXIMATION, the inner branch clears `[]` while the other association appends: the
    two sides are still equal because a PROVEN certificate's ledger is ALREADY `[]`
    (`ledger_eq_nil_of_ne`, §8). So the ledger case is guard algebra + the stored
    invariant, which is exactly why §8 exports that lemma.

  LAW 2 — EXHAUSTIVE + MUTUALLY EXCLUSIVE states (Phase 3, Theorem 2).
    A statement about the constructors of the flat enum `State` (§1): `decide`, with
    `Fintype.card State = 4` available from the derived `Fintype`.

  LAW 3 — BUDGET MONOTONICITY (Phase 3, Theorem 3).
    `spentEps`/`spentDelta` never decrease under `Budget.charge`: `drvEps` is monotone in
    `k` and in ε (using `eps_nonneg`, `dp_pos`, `dp_le1`, so `ln(1/δ') ≥ 0` and
    `e^ε − 1 ≥ 0`), and `ledgerEpsMax` is monotone under append. Corollary:
    `exhausted B → exhausted (B.charge r)`.

  LAW 4 — EXHAUSTION SOUNDNESS (Phase 3, Theorem 4).
    An exhausted budget never mints an APPROXIMATION: `issue`'s gate refuses whenever
    `(B.charge r).exhausted`, which under Law 3 is implied by `exhausted B`; the fallback
    path is confined to `{ESCALATED, TERMINATED}` by the `Fallback` type (§11). Also
    Phase 3: the exact homogeneous-DRV lemma flagged in §9.

  STRUCTURAL NON-LAW — "PROVEN ∘ PROVEN draws no budget."
    Not a theorem to prove: `compose : Certificate Ω → Certificate Ω → Certificate Ω`
    does not mention `Budget` in its type at all. No composition — of any states —
    can touch the accountant. Budget moves only through `Budget.charge`, and the only
    caller of `charge` in the calculus is `issue`. -/

/-!
============================================================================
  PHASE 3 — THE FOUR THEOREMS
============================================================================
-/

/-! ## 13. Theorem 1 — composition is associative

Componentwise via `Certificate.ext` (§4's `@[ext]`), per the §12 Law-1 route:
scope by `Set.inter_assoc`, state by `decide` over the 4-element enum (case-split
first — a named-binder `decide` would hit free variables), ledger by guard analysis
plus the stored invariant. The one asymmetric ledger case — an inner pair meeting at
PROVEN inside a triple meeting at APPROXIMATION — closes because both inner members
are then PROVEN and `ledger_eq_nil_of_ne` (§8) makes their ledgers `[]`, so clearing
and appending coincide. No DRV arithmetic appears anywhere in this proof: that is the
ledger design doing exactly the job it was chosen for (§2). -/

namespace State

/-- The weakest-member meet is associative. Finite case analysis; no order instance
needed. -/
theorem meet_assoc (a b c : State) : (a.meet b).meet c = a.meet (b.meet c) := by
  cases a <;> cases b <;> cases c <;> decide

end State

namespace Certificate

/-- **Theorem 1.** Composition of certificates is associative. -/
theorem compose_assoc (c d e : Certificate Ω) :
    (c.compose d).compose e = c.compose (d.compose e) := by
  have hmeet := State.meet_assoc c.state d.state e.state
  ext1
  · exact Set.inter_assoc _ _ _
  · simpa [compose] using hmeet
  · -- Ledger leg: both associations normalize to `c.ledger ++ d.ledger ++ e.ledger`
    -- when the triple meet is APPROXIMATION, and to `[]` otherwise.
    show (if (c.state.meet d.state).meet e.state = State.APPROXIMATION
            then (if c.state.meet d.state = State.APPROXIMATION
                    then c.ledger ++ d.ledger else []) ++ e.ledger
            else [])
        = (if c.state.meet (d.state.meet e.state) = State.APPROXIMATION
            then c.ledger ++ (if d.state.meet e.state = State.APPROXIMATION
                                then d.ledger ++ e.ledger else [])
            else [])
    rw [← hmeet]
    by_cases h3 : (c.state.meet d.state).meet e.state = State.APPROXIMATION
    · simp only [h3, if_true]
      by_cases h12 : c.state.meet d.state = State.APPROXIMATION
      · by_cases h23 : d.state.meet e.state = State.APPROXIMATION
        · simp [h12, h23, List.append_assoc]
        · -- Triple meet = A but d ⊓ e ≠ A: forces d = e = PROVEN, whose ledgers are [].
          have hde : d.state ≠ State.APPROXIMATION ∧ e.state ≠ State.APPROXIMATION := by
            revert h3 h12 h23
            cases c.state <;> cases d.state <;> cases e.state <;> decide
          simp [h12, h23, d.ledger_eq_nil_of_ne hde.1, e.ledger_eq_nil_of_ne hde.2]
      · -- Triple meet = A but c ⊓ d ≠ A: forces c = d = PROVEN, whose ledgers are [].
        have hcd : c.state ≠ State.APPROXIMATION ∧ d.state ≠ State.APPROXIMATION := by
          revert h3 h12
          cases c.state <;> cases d.state <;> cases e.state <;> decide
        have h23 : d.state.meet e.state = State.APPROXIMATION := by
          revert h3 h12
          cases c.state <;> cases d.state <;> cases e.state <;> decide
        simp [h12, h23, c.ledger_eq_nil_of_ne hcd.1, d.ledger_eq_nil_of_ne hcd.2]
    · simp [h3]

end Certificate

/-! ## 14. Theorem 2 — the four states are exhaustive and mutually exclusive

Statements about the constructors of the flat enum themselves (§1's design point): no
tag projection, no payload. Both discharge by `decide` (per the Phase-2 finding, the
∀-form is used so `decide` sees no free variables). `Fintype.card State = 4` pins the
count: exactly four states — SKIPPED is not among them, by type, not convention. -/

namespace State

/-- **Theorem 2a (exhaustive).** Every state is one of the four. -/
theorem exhaustive :
    ∀ s : State, s = PROVEN ∨ s = APPROXIMATION ∨ s = ESCALATED ∨ s = TERMINATED := by
  decide

/-- **Theorem 2b (mutually exclusive).** No state is two of the four at once: the four
constructors are pairwise distinct. -/
theorem mutually_exclusive :
    PROVEN ≠ APPROXIMATION ∧ PROVEN ≠ ESCALATED ∧ PROVEN ≠ TERMINATED ∧
    APPROXIMATION ≠ ESCALATED ∧ APPROXIMATION ≠ TERMINATED ∧ ESCALATED ≠ TERMINATED := by
  decide

/-- **Theorem 2c (count).** There are exactly four states — no fifth state exists in
which non-evaluation (or anything else) could hide. -/
theorem card_eq_four : Fintype.card State = 4 := by
  decide

end State

/-! ## 15. Theorem 3 — budget monotonicity: composed risk never decreases

The accountant's two spend axes, `spentEps` and `spentDelta`, never decrease under
`Budget.charge`. Route (§12 Law 3): `drvEps` is monotone in `k` and in ε — the side
conditions (`0 ≤ ε`, `0 < δ' ≤ 1`, hence `ln(1/δ') ≥ 0` and `e^ε − 1 ≥ 0`) come from
the proof fields the Phase-1 types carry, which is exactly why they were made fields —
and `ledgerEpsMax` is non-negative and monotone under append. The corollary
`exhausted_charge` (an exhausted budget stays exhausted, whatever is charged next) is
the bridge Theorem 4 consumes. -/

/-- `ledgerEpsMax` is non-negative: the fold base is 0 and every stored ε is ≥ 0. -/
theorem ledgerEpsMax_nonneg (l : List RiskParams) : 0 ≤ ledgerEpsMax l := by
  induction l with
  | nil => simp [ledgerEpsMax]
  | cons r t ih => exact le_max_of_le_right ih

/-- `ledgerEpsMax` never decreases when a mechanism is appended. -/
theorem ledgerEpsMax_le_append (l : List RiskParams) (r : RiskParams) :
    ledgerEpsMax l ≤ ledgerEpsMax (l ++ [r]) := by
  induction l with
  | nil => simp [ledgerEpsMax]
  | cons s t ih => exact max_le_max_left s.eps ih

/-- `drvEps` is monotone in both `k` and ε, under the side conditions the types carry:
`0 ≤ ε₁` and `δ' ∈ (0,1]`. Both DRV summands are products of factors that are
simultaneously non-negative and non-decreasing in `(k, ε)`. -/
theorem drvEps_mono (k₁ k₂ : ℕ) (e₁ e₂ dp : ℝ) (hk : k₁ ≤ k₂) (he : e₁ ≤ e₂)
    (he₁ : 0 ≤ e₁) (hdp : 0 < dp) (hdp1 : dp ≤ 1) :
    drvEps k₁ e₁ dp ≤ drvEps k₂ e₂ dp := by
  have hlog : 0 ≤ Real.log (1 / dp) :=
    Real.log_nonneg (by rw [le_div_iff₀ hdp]; linarith)
  have hkk : (k₁ : ℝ) ≤ (k₂ : ℝ) := Nat.cast_le.mpr hk
  have hexp : 0 ≤ Real.exp e₁ - 1 := by
    have := Real.add_one_le_exp e₁; linarith
  have he₂ : 0 ≤ e₂ := le_trans he₁ he
  unfold drvEps
  gcongr

/-- **Theorem 3a.** The accounted ε-spend never decreases under a charge. -/
theorem spentEps_mono (B : Budget) (r : RiskParams) :
    spentEps B ≤ spentEps (B.charge r) := by
  unfold spentEps Budget.charge
  exact drvEps_mono _ _ _ _ _
    (by simp)
    (ledgerEpsMax_le_append B.spent r)
    (ledgerEpsMax_nonneg B.spent)
    B.dp_pos B.dp_le1

/-- **Theorem 3b.** The accounted δ-spend never decreases under a charge. -/
theorem spentDelta_mono (B : Budget) (r : RiskParams) :
    spentDelta B ≤ spentDelta (B.charge r) := by
  unfold spentDelta Budget.charge
  simpa using r.delta_nonneg

/-- **Corollary (the Theorem-4 bridge).** Once exhausted, always exhausted: no charge
can bring an exhausted budget back inside its ceilings. -/
theorem exhausted_charge {B : Budget} (h : B.exhausted) (r : RiskParams) :
    (B.charge r).exhausted := by
  rcases h with h | h
  · exact Or.inl (lt_of_lt_of_le h (spentEps_mono B r))
  · exact Or.inr (lt_of_lt_of_le h (spentDelta_mono B r))

/-! ## 16. Theorem 4 — exhaustion soundness

Once the budget is spent, `issue` cannot produce an APPROXIMATION: its output lands in
{ESCALATED, TERMINATED}, and the budget is returned untouched (a refusal draws nothing).

SCOPE OF THE CLAIM (per §11's documented limitation): this is a theorem about `issue`'s
OUTPUT — the calculus's only budget-consulting mint. It is NOT the false stronger claim
that no APPROXIMATION term can exist without a budget: `Certificate.approx` (§4) can
inhabit the type directly. The honest reading: any certificate whose issuance respected
the accountant went through `issue`, and `issue` respects exhaustion — proved below. -/

open Classical in
/-- **Theorem 4a (exhaustion soundness).** An exhausted budget never mints an
APPROXIMATION: the issued certificate is the caller's fallback — ESCALATED or
TERMINATED, nothing else — and the budget comes back unchanged. -/
theorem issue_exhausted {B : Budget} (h : B.exhausted) (scope : Set Ω) (r : RiskParams)
    (fb : Fallback) :
    (issue B scope r fb).1 = fb.certificate scope ∧ (issue B scope r fb).2 = B := by
  have hpost : (B.charge r).exhausted := exhausted_charge h r
  unfold issue
  rw [if_neg (not_not_intro hpost)]
  exact ⟨rfl, rfl⟩

open Classical in
/-- **Theorem 4b (the spec's phrasing).** Once the budget is spent, no APPROXIMATION
certificate can be issued: the output state is never APPROXIMATION — positively, it is
ESCALATED or TERMINATED. -/
theorem issue_exhausted_state {B : Budget} (h : B.exhausted) (scope : Set Ω)
    (r : RiskParams) (fb : Fallback) :
    (issue B scope r fb).1.state = State.ESCALATED ∨
    (issue B scope r fb).1.state = State.TERMINATED := by
  rw [(issue_exhausted h scope r fb).1]
  cases fb
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ## 17. The exact homogeneous-DRV lemma (user ruling R3: "both, labeled")

This is the second half of the R3 ruling, promised in §9. The two halves, labeled:

  * HETEROGENEOUS ledger (§9's accountant, always applicable): `spentEps` evaluates DRV
    at ε_max — an OVER-APPROXIMATION whose soundness as a bound on the true composed
    loss rests on DP's monotonicity in ε, which is CITED, NOT FORMALIZED.

  * HOMOGENEOUS ledger (this section): when every charged mechanism carries the SAME ε
    — the exact hypothesis under which Dwork–Rothblum–Vadhan state their theorem, "k
    mechanisms each (ε,δ)" — the accountant's value IS the paper's bound, exactly:
        spentEps  = √(2k·ln(1/δ'))·ε + k·ε·(e^ε − 1)      (k = number of mechanisms)
        spentDelta = k·δ + δ'
    with ZERO unformalized assumptions: the ε_max over-approximation degrades to an
    equality (`ledgerEpsMax` of an all-ε ledger is ε), so nothing rests on the cited
    DP fact. Proved below, including the empty ledger (k = 0, both sides vanish — no
    non-emptiness hypothesis on the headline lemmas). -/

/-- With no mechanisms charged, the DRV bound is zero regardless of ε: both summands
carry a factor of `k = 0`. -/
theorem drvEps_zero (e dp : ℝ) : drvEps 0 e dp = 0 := by
  simp [drvEps]

/-- On a non-empty all-ε ledger, the worst case IS the common ε: the over-approximation
is exact. (Non-emptiness is needed here — `ledgerEpsMax [] = 0` — but not in the
headline lemmas below, where `k = 0` kills ε anyway.) -/
theorem ledgerEpsMax_homogeneous {l : List RiskParams} {e₀ : ℝ} (hne : l ≠ [])
    (hall : ∀ r ∈ l, r.eps = e₀) : ledgerEpsMax l = e₀ := by
  induction l with
  | nil => exact absurd rfl hne
  | cons r t ih =>
    have hr : r.eps = e₀ := hall r (by simp)
    rcases eq_or_ne t [] with ht | ht
    · subst ht
      show max r.eps 0 = e₀
      rw [max_eq_left r.eps_nonneg, hr]
    · have hIH := ih ht (fun s hs => hall s (by simp [hs]))
      show max r.eps (ledgerEpsMax t) = e₀
      rw [hr, hIH, max_self]

/-- **Homogeneous DRV, ε axis.** If every charged mechanism has the same ε, the
accounted ε-spend is EXACTLY the DRV bound at that ε with k = the number of mechanisms.
No DP assumption, no over-approximation. -/
theorem spentEps_homogeneous {B : Budget} {e₀ : ℝ}
    (hall : ∀ r ∈ B.spent, r.eps = e₀) :
    spentEps B = drvEps B.spent.length e₀ B.deltaPrime := by
  rcases eq_or_ne B.spent [] with h | h
  · unfold spentEps
    simp [h, ledgerEpsMax, drvEps_zero]
  · unfold spentEps
    rw [ledgerEpsMax_homogeneous h hall]

/-- The sum of a constant-δ ledger's deltas is `k·δ`. -/
theorem sum_map_delta_homogeneous (d₀ : ℝ) (l : List RiskParams) :
    (∀ r ∈ l, r.delta = d₀) → (l.map (·.delta)).sum = l.length * d₀ := by
  induction l with
  | nil => intro _; simp
  | cons r t ih =>
    intro hall
    have hr : r.delta = d₀ := hall r (by simp)
    have hIH := ih (fun s hs => hall s (by simp [hs]))
    simp [hr, hIH]
    ring

/-- **Homogeneous DRV, δ axis.** If every charged mechanism has the same δ, the
accounted δ-spend is EXACTLY `k·δ + δ'` — the DRV total, with δ' counted once. -/
theorem spentDelta_homogeneous {B : Budget} {d₀ : ℝ}
    (hall : ∀ r ∈ B.spent, r.delta = d₀) :
    spentDelta B = B.spent.length * d₀ + B.deltaPrime := by
  unfold spentDelta
  rw [sum_map_delta_homogeneous d₀ B.spent hall]

end VCalc
