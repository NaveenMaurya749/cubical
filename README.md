# cubical

This is the repository for my Bachelor's Thesis at IISc during 2026 advised by Prof Siddhartha Gadgil, on the topic of investigating
a variety of foundational systems called Type Theories, namely Martin-Löf Type Theory, Homotopy Type Theory and Cubical Type Theory.
The report and slides for presentation were submitted by May 01, 2026.

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
