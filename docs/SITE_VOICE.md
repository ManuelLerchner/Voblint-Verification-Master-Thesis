# Voice of the project site

How `pages/index.html` is written. The page reads as a long blog post for a
programmer who knows neither abstract interpretation nor Isabelle. The claim
rules of `CLAUDE.md` (what is proved, trusted, defined, tested) apply in full;
this file only covers how the prose sounds.

## Structure

- Open a section with a situation, a program or an event, then the idea it
  needs. A claim comes after the example that motivates it, never before.
- Head a section with the reader's question ("What if the analyzer is wrong?")
  or a plain phrase. No slogans.
- Introduce a term the moment it is needed, in one clause ("a context is the
  part of the call history the analysis keeps"), not in a definition block.
- An Isabelle name follows the idea it stands for, as a link the reader may
  skip. It never carries the sentence.
- End a section where its idea ends. No summary, no "in short".

## Sentences

- Address the reader as "you"; the author may say "we" for what the project
  did. Questions the reader would ask may be asked, then answered at once.
- Mix short and long sentences. One idea per sentence.
- Plain verbs and nouns. Concrete numbers and names where they exist: a pull
  request, a revision, a line count, a step count.
- Name limits where they apply, in the same plain tone as the claims.

## Avoid

- Aphorisms that stand in for an explanation ("the reason is shape", "being
  local is what fixes that"). Say the mechanism.
- Decorative contrasts ("not X, but Y", "X rather than Y") unless both sides
  are real alternatives.
- Colon reveals, stacked clauses, three-item lists by habit.
- Hype ("powerful", "robust", "transformative") and slang or memes. Humour, if
  any, is rare and dry.
