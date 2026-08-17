# cubical

This is the repository for my Bachelor's Thesis at IISc during 2026 advised by Prof Siddhartha Gadgil, on the topic of investigating
a variety of foundational systems called Type Theories, namely Martin-Löf Type Theory, Homotopy Type Theory and Cubical Type Theory.
The report and slides for presentation were submitted by May 01, 2026.

## Abstract

We survey three foundational frameworks in modern type theory: Martin-Löf Type Theory (MLTT), Homotopy Type
Theory (HoTT), and Cubical Type Theory. We begin with MLTT as a deductive system based on dependent λ-calculus,
emphasizing inductive types and type formers, including W-types. We then present HoTT’s homotopical interpretation of
types, where identity types correspond to path spaces, and discuss key principles such as univalence and higher inductive
types. Motivated by limitations in the computational behavior of HoTT, we introduce Cubical Type Theory via cubical
sets, highlighting its improved properties, including computational univalence, canonicity, and normalization.

## Contents so far

```
cubical/                -- repository
├── Cubical/            -- nothing yet
├── HoTT/               -- Interactive exercises from the HoTT book
│ ├── MyEq.lean         -- Custom inductive type of equality
│ ├── Tactics.lean      -- Custom defined tactics such as `pathind`
│ ├── chapter1.lean     -- Exercises from Chapter 1
│ └── chapter2.lean     -- Exercises from Chapter 1
├── LaTeX/              -- LaTeX source for thesis report and presentation
│ ├── presentation/     -- LaTeX source for final presentation
│ | └── main.pdf        -- Compiled pdf
│ └── thesis/           -- LaTeX source for final report submission
│ | └── main.pdf        -- Compiled pdf
├── Cubical.lean        -- imports all modules from Cubical/
├── HoTT.lean           -- imports all modules from HoTT/
├── Main.lean           -- root file to be built
└── README.md           -- readme
```

## Releases

The releases consist of the final report and slides for presentation held on May 01, 2026.
