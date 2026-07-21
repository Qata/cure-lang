# Type-system specification family

The dependent-kernel specifications govern type formation and conversion;
these documents govern source-level type features and elaboration extensions.

The overload documents form one staged feature family rather than competing
designs:

1. `2026-07-10-typeclasses-design.md` defines compile-time dictionaries and
   coherence.
2. `2026-07-09-typeclasses-elaborator-feature-design.md` defines why and how
   `proto`/`impl` are elaborator features rather than macros.
3. `2026-07-10-overloading-and-argument-labels-design.md` defines labelled
   parameter and overload identity rules.
4. `2026-07-18-type-directed-overload-resolution-design.md` defines the first
   type-directed resolution slice.
5. `2026-07-18-precedence-groups-and-operator-overloading-design.md` extends
   that machinery to operators and fixity.

The later documents refine the earlier ones; they do not introduce separate
overload systems. When they disagree, the newest approved document and the
implementation gate it names govern.
