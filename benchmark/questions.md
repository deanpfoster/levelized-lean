# Header vs Source Comprehension Benchmark

## Method

For each module, ask 3 questions. Run twice: once with header only, once with full source.
Score: correct/incorrect. Measure token count consumed.

## Modules (10 modules, covering different areas)

1. MergeSort (Algorithms)
2. LTS.Bisimulation (Foundations)
3. Data.Relation (Foundations)
4. CCS.BehaviouralTheory (Languages)
5. CombinatoryLogic.Confluence (Languages)
6. PerfectSecrecy.Basic (Crypto)
7. OmegaLanguage (Computability)
8. Stlc.Safety (Languages/LambdaCalculus)
9. HML.Basic (Logics)
10. RegularLanguage (Computability)

## Questions per module

Q1 (existence): "Does this module prove [specific claim]?" (yes/no + name if yes)
Q2 (type): "What is the exact type signature of [theorem name]?"
Q3 (usage): "I want to prove [goal]. Which theorem(s) from this module should I use?"

## Scoring

- Q1: 1 point for correct yes/no, 0.5 bonus for correct theorem name
- Q2: 1 point for exact match, 0.5 for close (right structure, wrong detail)
- Q3: 1 point for identifying the right theorem(s), 0.5 for partial
