# Benchmark Results: Headers vs Source Comprehension

## Scoring

Each question scored 0-1.5:
- 1.0 for correct answer
- 0.5 bonus for exact theorem name or type signature
- 0 for wrong or NOT FOUND when answer exists

## Results by Module

| Module | Q | Header Score | Source Score | Notes |
|--------|---|-------------|-------------|-------|
| MergeSort | Q1 | 1.5 | 1.5 | Both correct + exact name |
| | Q2 | 1.5 | 1.5 | Both exact type |
| | Q3 | 1.5 | 1.5 | Both correct |
| Bisimulation | Q1 | 1.5 | 1.5 | Both found eqv; source found additional weak variant |
| | Q2 | 1.5 | 1.5 | Both exact; source gave 2 variants |
| | Q3 | 1.5 | 1.5 | Both correct |
| Relation | Q1 | 1.5 | 1.5 | Both found Newman's Lemma |
| | Q2 | 1.5 | 1.5 | Both found iff + direction |
| | Q3 | 1.5 | 1.5 | Both correct |
| CCS | Q1 | 1.5 | 1.5 | Both found par_comm |
| | Q2 | 1.5 | 1.5 | Both exact; source used notation |
| | Q3 | 1.5 | 1.5 | Both found par_nil |
| Confluence | Q1 | 1.5 | 1.5 | Both found MRed.diamond |
| | Q2 | 1.5 | 1.5 | Both exact |
| | Q3 | 1.5 | 1.5 | Both correct |
| PerfectSecrecy | Q1 | 1.5 | 1.5 | Both found Shannon's theorem |
| | Q2 | 1.5 | 1.5 | Both exact |
| | Q3 | 1.5 | 1.5 | Both correct |
| OmegaLanguage | Q1 | 0 | 0 | Both correctly said NOT FOUND |
| | Q2 | 1.5 | 1.5 | Header: ω_omegaPow_coind; Source: omegaPow_coind (same theorem, different name form) |
| | Q3 | 1.5 | 1.5 | Both found kstar equality |
| STLC Safety | Q1 | 1.5 | 1.5 | Both found progress |
| | Q2 | 1.5 | 1.5 | Both exact; source used notation |
| | Q3 | 1.5 | 1.5 | Both correct |
| HML | Q1 | 1.5 | 1.5 | Both found theoryEq_eq_bisimilarity |
| | Q2 | 1.5 | 1.5 | Both exact |
| | Q3 | 1.5 | 1.5 | Both correct |
| RegularLanguage | Q1 | 1.5 | 1.5 | Header: reg_compl; Source: IsRegular.compl (same thm) |
| | Q2 | 1.5 | 1.5 | Both exact |
| | Q3 | 1.5 | 1.5 | Header: reg_inf; Source: IsRegular.inf |

## Summary

| Metric | Headers | Source |
|--------|---------|-------|
| Total Score | 43.5 / 45 | 43.5 / 45 |
| Accuracy | 97% | 97% |
| Questions with exact answer | 29/30 | 29/30 |
| NOT FOUND (correct) | 1 | 1 |

## Qualitative Differences

**Accuracy: TIE.** Both agents answered all 30 questions correctly. Neither hallucinated.

**Specificity:** The source agent gave richer answers — citing line numbers, showing
alternative theorems, explaining notation. The header agent gave cleaner, more
focused answers — one theorem per question, exact reference to ExternalTheorem entry.

**Name precision:** The header agent used the header's alias names (e.g., `reg_compl`,
`bisimilarity_le_traceEq`). The source agent used the original fully-qualified names
(e.g., `IsRegular.compl`, `Bisimilarity.le_traceEq`). Both are correct but reference
different name forms.

## The Real Difference: Cost

| Metric | Headers | Source |
|--------|---------|-------|
| Lines read | ~3,600 | ~6,400 (10 files, not all 20K) |
| Tool calls to read files | 12 | 13 |
| Agent duration | ~85s | ~106s |
| Token cost (total) | ~42K | ~72K |

**The header agent used 42% fewer tokens for the same accuracy.**

## Conclusion

For well-written code (like CSLib with good docstrings), accuracy is the same.
The header advantage is **efficiency**: 42% fewer tokens, 20% faster, cleaner answers.

The header advantage would be larger for:
- Poorly documented code (no docstrings, cryptic names)
- Larger modules where proof noise dominates
- LLMs with smaller context windows where 20K lines wouldn't fit
- Repeated queries (amortized vocabulary cost)

The header advantage is NOT about accuracy for high-quality code — it's about
cost, speed, and scalability.
