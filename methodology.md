# Methodology

This document explains how I work on this project, and how I will use AI.

## Previous

I started by reading the sections concerning LTL in Ben-Ari's "Mathematical Logic for Computer Science" while taking notes. I used AI only to ask for clarifications and further explanations.

Then I followed the proof procedure described in the book by hand to prove that (|= Fp -> Gp) and (|= G(p v q) -> (Gp v Gq)) are not valid. These formulas came by asking AI for formulas to prove by hand are not valid. I made these proofs in Typst, and I used AI to write the formatting code. However, the actual proof content was 100% made manually.

I also proved that some formulas are valid in Typst, but not via the method used in the book since it was not actually fully explained.

Next task was to understand the code in the repository. I started by reading m4.pdf while taking notes. I used AI to explain anything I didn't understand. Then I started trying to understand how m4.pdf was implemented in the repository, but this was hard since the repository contains ~7000 lines of code. I used AI to make the code more readable without changing its actual content. Changes made are:

- Formula syntax in unicode
- Proof renderer
- More unicode names.
- Clearer names.
- Name repeated hypothesis and share leading signature arguments.
- Make the graph code generic over node type.
- Single variant datatypes turned into records.
- Simplify Boolean case splits, reuse list lemmas, share P in module blocks.

These were made with very little oversight by me.

To understand how the code works I used AI to create an interactive guide for me how m4.pdf maps to the code.

Next I wanted to understand m5.pdf. To save time I asked the AI to create one interactive guide going over both theory and codebase. I do not think this was very effective, as it was "too easy". It was easy skim, or think I understand something without actually doing it.

## Future

This is how I plan to proceed from here.

### Trusted core

Agda ensures that the proofs produced by AI are correct, but if the theorem is wrongly stated this means nothing. I will thus manually create a "Trusted" module that contains the theorem specification: what this project aims to prove. This module should be self-sufficient, and the AI will never be allowed to change it. It should be as small and readable as possible to ensure correctness.
