# Dialect Ideas Backlog — 50 Unspecced Designs

**Date:** 2026-07-08
**Status:** idea backlog (operator-requested). None of these are specced;
each entry is a name, a pitch, and the invisible-machinery hook. Promotion
path: pick one → full child spec in this directory following the established
template. The premise throughout is the dialect facility
(`2026-07-08-dialect-facility-design.md`): every one of these is library
work, zero compiler changes. The brief was to think across *all* the niche
ways people interact with programming — not just MCUs.

Legend for hooks: **R** refinements · **T** typestate/GADT index · **U** units
· **C** coverage/totality · **F** flow/causality · **E** effects/IFC ·
**K** check templates · **P** projection/purity.

---

## Physical computing & electronics

1. **`wiring`** — declare the *physical* circuit (components, which leg on
   which pin, resistor values); cross-checked against the board's
   capabilities, generates the wiring diagram AND the `let` bindings so code
   and breadboard cannot drift. Inductive-load-without-flyback warnings. R,U
2. **`power`** — battery capacity + per-task duty cycles → compile-time
   battery-life estimate; deep-sleep typestate requires peripherals released;
   mA/mAh units end to end. T,U
3. **`display`** — declarative widget layout for OLED/e-paper; layouts
   checked against resolution/color depth at compile time; e-paper
   partial-refresh regions typed so full-refresh ghosting is a choice, not a
   surprise. R,T
4. **`motion`** — stepper/servo motion profiles; soft limits as refinements
   on the machine's travel envelope; acceleration continuity checked; mm and
   mm/s everywhere. R,U
5. **`pid`** — control loops with units-checked gains, anti-windup by
   construction, and sample-time consistency verified against the `every`
   task driving it. U,C

## Machines & fabrication

6. **`gcode`** — CNC/3D-printer jobs as typed toolpaths; feeds/speeds
   united; every move checked against the declared machine envelope —
   crashing the spindle into the vise becomes a compile error. R,U
7. **`modbus`** — PLC/industrial register maps (the `driver` pattern for
   factory gear); function-code and register-width correctness by
   construction. T,R
8. **`canbus`** — CAN frame databases (DBC-style); signal packing rides the
   `packet` machinery; bus-load percentage estimated at compile time from
   declared cycle times. R,U
9. **`keymap`** — custom keyboard firmware (the QMK niche); layers as a
   state machine with reachability checking; chord conflicts and unreachable
   layers flagged. T,C
10. **`behavior`** — behavior trees for hobby robotics; tick totality means
    a robot brain that provably cannot hang; blackboard reads require prior
    writes. C,T

## Home & environment

11. **`home`** — automation rules (trigger/condition/action); two rules
    fighting over one actuator is detected the way `fleet` detects
    unprojectable state — a named conflict with named resolutions. P,C
12. **`alarm`** — security zones; armed/entry-delay/triggered typestate;
    every sensor must belong to a zone (coverage); exit paths must have
    delays. T,C
13. **`energy`** — tariffs + declared loads → cost simulation; kWh/kW units;
    "the heater never runs during peak pricing" is a check prop over the
    schedule. U,K
14. **`climate`** — HVAC schedules with hysteresis; deadband refinements
    make heat-and-cool-fighting structurally impossible. R,U
15. **`grow`** — greenhouse/hydroponics recipes: staged light/nutrient
    schedules, pH/EC refinements on dosing, pump interlocks (total flow ≤
    pump capacity as a refinement across zones). R,U,T

## Food & craft

16. **`brew`** — fermentation profiles (multi-day temperature ramps) driving
    hardware; stage typestate gated on sensor evidence — no bottling until
    gravity is stable. T,U
17. **`knit`** — knitting/weaving patterns; stitch counts must balance row
    to row (the compile error every knitter has wanted for two centuries);
    yardage computed from the pattern. R,C

## Science, data & lab

18. **`table`** — dataframe pipelines with schema- and unit-checked columns;
    joins on typed keys; silently-row-dropping aggregations are lints. R,U
19. **`plot`** — charts declared against table schemas; axes inherit column
    units automatically; impossible encodings (a categorical on a continuous
    scale) rejected. U,C
20. **`stats`** — declared hypotheses and tests; assumption obligations
    (sample size, paired-ness) must be discharged before a p-value renders —
    the analysis equivalent of typestate. T,K
21. **`labproto`** — lab protocols with unit-checked volumes/timings;
    generates bench checklists and device timers; reagent totals computed;
    a step using an unprepared solution is unrepresentable. T,U
22. **`notebook`** — literate documents whose cells form a dataflow graph;
    stale-cell output is impossible by construction (re-run is the flow
    propagating), runs are deterministic and seeded. F,P

## Teaching & learning

23. **`turtle`** — turtle graphics where totality guarantees every drawing
    finishes; angles/distances united; the gentlest on-ramp to the whole
    language. C,U
24. **`lesson`** — curricula with embedded exercises verified by `check`;
    the prerequisite graph is acyclic by construction; a lesson referencing
    an untaught concept is a compile error. C,K
25. **`automata`** — DFA/NFA/Turing machines for CS courses; equivalence and
    minimization checked; diagrams generated; the pumping lemma as a check
    counterexample generator. K,C
26. **`blocks`** — the meta-dialect: export any dialect's declarative
    grammar as a Blockly-style visual block palette, giving every other
    entry in this file a drag-and-drop mode for free. (Pure dividend of
    grammar-as-data.) —
27. **`roll`** — tabletop rules: dice expressions, character sheets with
    stat invariants; probability distributions computed at compile time so
    the DM sees exact odds next to every roll. R,K

## Games & stories

28. **`scene`** — 2D sprite scenes; asset references are compile-checked
    (missing PNG = build error, not black square); z-order/layers typed. R,C
29. **`dialogue`** — branching dialogue trees; reading a story flag requires
    a path that set it (typestate over narrative state); orphan branches
    flagged. T,C
30. **`quest`** — quest/achievement graphs with static liveness: every quest
    reachable AND completable, checked like `fsm` reachability. C
31. **`cards`** — card-game rules; deck composition refinements (exactly 60
    cards, ≤4 per name); costs united; shuffles seeded so bug reports
    replay. R,K

## Music, stage & performance

32. **`score`** — traditional notation where measures must sum to the time
    signature (a refinement musicians already think in); transposition is
    total; MIDI/MusicXML out. R,C
33. **`synth`** — patch/signal-routing graphs; a feedback loop without a
    delay element is rejected by exactly the FRP causality index that
    protects `flow` — same theorem, new audience. F
34. **`choreo`** — lighting/laser/drone show cues on the `pattern` clock;
    safety envelopes (drone no-fly boxes, laser exposure limits) as
    refinements — art with a safety case. R,U,F

## Safety-critical hobbies

35. **`dive`** — recreational dive planning: no-decompression limits,
    ascent rates, and gas mixes as refinements — a domain where the type
    error is literally the safety event. R,U
36. **`ham`** — amateur radio: frequencies/power refinement-checked against
    band plans AND the operator's declared license class; logging formats
    via `packet`. R
37. **`checklist`** — aviation-style checklists as typestate: items
    complete in order, challenge-response pairs total, abnormal branches
    reachable; renders to kneeboard cards and cockpit displays. T,C
38. **`rocketry`** — model rocketry: motor class vs. airframe mass
    refinements, recovery-deploy altitude windows, field waiver ceiling as
    a bound; simulation hooks via `sim`. R,U,K
39. **`drone`** — flight plans with geofence and battery-reserve
    refinements (return-to-home energy provably reserved); mission steps as
    a reducer. R,U,T

## Ops & infrastructure

40. **`netpolicy`** — firewall/routing rules where shadowed or unreachable
    rules are compile errors and policy diffs are semantic, not textual. C
41. **`deploy`** — BEAM release topology (hosts, releases, health checks,
    rolling order) — `fleet`'s cousin for servers, same projection honesty
    (`cure deploy report`). P
42. **`backup`** — backup policies where restore is verified by
    construction (`check` runs an actual restore in sim); GFS retention
    algebra validated. K
43. **`alert`** — metrics and alerts; thresholds carry units; overlapping
    alerts are a fatigue lint; every alert must name a runbook (totality of
    response). U,C

## Office, money & time

44. **`ledger`** — double-entry bookkeeping: transactions balance by
    construction; currencies are units that never mix without a declared
    conversion at a declared rate. R,U
45. **`pricing`** — discount/promo stacking rules; no-negative-total and
    stacking idempotence checked; the effective-price table is generated,
    not discovered in production. R,K
46. **`rota`** — shift scheduling; rest-period and qualification constraints
    as refinements; double-booking inexpressible; fairness metrics computed
    at compile time. R,C
47. **`recur`** — calendar recurrence (the RFC-5545/DST minefield) behind a
    checked surface; timezone transitions are explicit values, and "skipped/
    doubled occurrence" bugs become visible at declaration time. R,K

## AI & language

48. **`prompt`** — typed prompt templates: placeholders bound (coverage),
    outputs parsed against a declared schema (the `parse` dialect pointed at
    an LLM) with a retry policy — and the IFC payoff: a `secret` cannot flow
    into a prompt without an audited `declassify`. C,E
49. **`agenttools`** — tool-using agent loops where every tool carries a
    capability effect; an agent is physically unable to call outside its
    declared manifest — effects as the sandbox. E,T
50. **`evals`** — LLM evaluation suites as `check` props: graded rubrics,
    seeded datasets, regression gates on model swaps, the three-rung ladder
    reporting which behaviors are guaranteed vs. sampled. K

---

Recurring observation across all fifty: the pattern from the parent spec
holds in every niche — *users declare domain facts; the compiler
manufactures types; errors speak the domain's vocabulary; every guarantee is
marketed as the disaster it prevents* (a spindle crash, a missed
decompression stop, an unbalanced ledger, a leaked API key, a knitting row
that doesn't add up).
