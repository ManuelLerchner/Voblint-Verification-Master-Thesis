# IMP2 Pretty Notation Migration

Status: **DONE** (Tier 3 implemented in `IMP2_Notation.thy`; bracket `⟦ ... ⟧` and whole-program `⟦ proc f { .. } main { .. } ⟧` live). Used in `Example_Side_Execute`, `Example_Proc_Call`, `IMP2_VCG_Example`.

## Problem

Example programs are written with fully-qualified constructors:

```isabelle
definition loop_prog :: "IMP2_Proc.com" where
  "loop_prog =
     IMP2_Proc.com.Seq
       (IMP2_Proc.com.Assign ''x'' (BaseN (AExp.N 0)))
       (IMP2_Proc.com.While (BaseB (BExp.Bc True))
          (IMP2_Proc.com.Assign ''x''
             (Plus (BaseN (AExp.V ''x'')) (BaseN (AExp.N 1)))))"
```

## What AutoCorrode Actually Does

AutoCorrode writes programs like this:

```isabelle
definition swap_client where
  "swap_client ≡ FunctionBody ⟦
    let mut left = ⟪42 :: nat⟫;
    let mut right = 72;
    swap_ref(left, right);
    *left
  ⟧"
```

The `⟦ ... ⟧` bracket is not `notation` — it's a **full embedded language parser**. The implementation (`Micro_Rust_Parsing_Frontend/Micro_Rust_Syntax.thy`) defines:

- A `nonterminal urust` category (separate from HOL's `logic`)
- Dozens of grammar productions covering the full Rust subset (operators, control flow, closures, structs, patterns, etc.)
- ML-level **parse AST translations** that convert the `urust` AST into underlying µRust monad constructors
- An antiquotation `⟪expr :: type⟫` to escape back to HOL terms when needed

The payoff: you write actual Rust inside the brackets; Isabelle treats it as a term.

## Three Tiers for IMP2

### Tier 1 — `notation` (Quick Win, No ML)

Mirror HOL-IMP's `Com.thy` convention in `IMP2_Proc.thy`:

```isabelle
notation
  IMP2_Proc.com.Assign ("_ ::= _"           [1000, 61] 61) and
  IMP2_Proc.com.Seq    ("_;;/ _"             [60, 61] 60) and
  IMP2_Proc.com.If     ("IF _ THEN _ ELSE _" [0, 0, 61] 61) and
  IMP2_Proc.com.While  ("WHILE _ DO _"       [0, 61] 61) and
  IMP2_Proc.com.Scope  ("SCOPE _"            [61] 61) and
  IMP2_Proc.com.Call   ("CALL _"             [1000] 61)
```

Combined with the existing `N`, `V`, `Bc` abbreviations:

```isabelle
definition loop_prog :: "IMP2_Proc.com" where
  "loop_prog = ''x'' ::= N 0 ;; WHILE Bc True DO (''x'' ::= Plus (V ''x'') (N 1))"
```

**Effort:** ~10 lines. **Limit:** still requires HOL string quotes `''x''` and prefix `Plus`/`Minus`.

---

### Tier 2 — `syntax` + `translations` (Medium, No ML)

Define a custom `nonterminal imp_stm` and grammar that gives block syntax.
Variable names stay as HOL strings, but sequencing, control flow, and structure improve:

```isabelle
nonterminal imp_stm

syntax
  "_imp_seq"    :: "imp_stm \<Rightarrow> imp_stm \<Rightarrow> imp_stm"
                    ("_;/ _"              [60,61] 60)
  "_imp_assign" :: "string \<Rightarrow> aexp \<Rightarrow> imp_stm"
                    ("_ := _"             [900,61] 61)
  "_imp_while"  :: "bexp \<Rightarrow> imp_stm \<Rightarrow> imp_stm"
                    ("while _ { _ }"      [0,61] 61)
  "_imp_if"     :: "bexp \<Rightarrow> imp_stm \<Rightarrow> imp_stm \<Rightarrow> imp_stm"
                    ("if _ { _ } else { _ }" [0,0,61] 61)
  "_imp_skip"   :: "imp_stm"             ("skip")
  "_imp_scope"  :: "imp_stm \<Rightarrow> imp_stm"  ("scope { _ }")
  "_imp_call"   :: "string \<Rightarrow> imp_stm"   ("call _ ;")
  "_IMP"        :: "imp_stm \<Rightarrow> IMP2_Proc.com" ("IMP { _ }")

translations
  "IMP { x := a ; rest }" \<rightleftharpoons>
      "CONST IMP2_Proc.com.Seq (CONST IMP2_Proc.com.Assign x a) (IMP { rest })"
  "IMP { x := a }"  \<rightleftharpoons> "CONST IMP2_Proc.com.Assign x a"
  "IMP { while b { body } ; rest }" \<rightleftharpoons>
      "CONST IMP2_Proc.com.Seq (CONST IMP2_Proc.com.While b (IMP { body })) (IMP { rest })"
  ...
```

Result:

```isabelle
definition loop_prog :: "IMP2_Proc.com" where
  "loop_prog = IMP {
     ''x'' := N 0;
     while Bc True { ''x'' := Plus (V ''x'') (N 1) }
   }"
```

**Effort:** ~50–80 lines. **Limit:** variable names still need `''x''` quotes; arithmetic still uses prefix `Plus`/`Minus`/`Times`.

---

### Tier 3 — Quotation Bracket with ML Parse Translation (AutoCorrode Style)

Define `IMP ⟦ ... ⟧` using Isabelle's `parse_translation` ML hook.
Inside the bracket, bare identifiers become string literals and numerals become `N n`.
This is IMP2's equivalent of AutoCorrode's `FunctionBody ⟦ ... ⟧`.

Target syntax:

```isabelle
definition loop_prog :: "IMP2_Proc.com" where
  "loop_prog = IMP ⟦
     x := 0;
     while true {
       x := x + 1
     }
   ⟧"
```

#### Implementation sketch

**Step 1: nonterminals and grammar** (in `IMP2_Notation.thy`)

```isabelle
nonterminal imp2_com imp2_aexp imp2_bexp

syntax
  "_IMP2"          :: "imp2_com \<Rightarrow> IMP2_Proc.com"  ("IMP _")
  "_imp2_seq"      :: "imp2_com \<Rightarrow> imp2_com \<Rightarrow> imp2_com"  ("_; _" [60,61] 60)
  "_imp2_assign"   :: "id \<Rightarrow> imp2_aexp \<Rightarrow> imp2_com"         ("_ := _" [900,61] 61)
  "_imp2_while"    :: "imp2_bexp \<Rightarrow> imp2_com \<Rightarrow> imp2_com"   ("while _ { _ }" [0,61] 61)
  "_imp2_if"       :: "imp2_bexp \<Rightarrow> imp2_com \<Rightarrow> imp2_com \<Rightarrow> imp2_com"
                       ("if _ { _ } else { _ }" [0,0,61] 61)
  "_imp2_skip"     :: "imp2_com"                              ("skip")
  "_imp2_scope"    :: "imp2_com \<Rightarrow> imp2_com"                ("scope { _ }")
  "_imp2_call"     :: "id \<Rightarrow> imp2_com"                       ("call _")
  (* aexp *)
  "_imp2_var"      :: "id \<Rightarrow> imp2_aexp"                      ("_")
  "_imp2_num"      :: "num_const \<Rightarrow> imp2_aexp"               ("_")
  "_imp2_plus"     :: "imp2_aexp \<Rightarrow> imp2_aexp \<Rightarrow> imp2_aexp"  ("_ + _" [65,66] 65)
  "_imp2_minus"    :: "imp2_aexp \<Rightarrow> imp2_aexp \<Rightarrow> imp2_aexp"  ("_ - _" [65,66] 65)
  "_imp2_times"    :: "imp2_aexp \<Rightarrow> imp2_aexp \<Rightarrow> imp2_aexp"  ("_ * _" [70,71] 70)
  (* bexp *)
  "_imp2_true"     :: "imp2_bexp"                             ("true")
  "_imp2_false"    :: "imp2_bexp"                             ("false")
  "_imp2_less"     :: "imp2_aexp \<Rightarrow> imp2_aexp \<Rightarrow> imp2_bexp"  ("_ < _" [50,51] 50)
  "_imp2_eq"       :: "imp2_aexp \<Rightarrow> imp2_aexp \<Rightarrow> imp2_bexp"  ("_ == _" [50,51] 50)
  "_imp2_and"      :: "imp2_bexp \<Rightarrow> imp2_bexp \<Rightarrow> imp2_bexp"  ("_ && _" [35,36] 35)
  "_imp2_or"       :: "imp2_bexp \<Rightarrow> imp2_bexp \<Rightarrow> imp2_bexp"  ("_ || _" [30,31] 30)
  "_imp2_not"      :: "imp2_bexp \<Rightarrow> imp2_bexp"               ("! _" [90] 90)
```

**Step 2: ML parse translation** (in the same theory, inside `ML { ... }` block)

The key job of the parse translation is:

- `Free("x", _)` in `imp2_aexp` position → `Const(@{const_name V}, _) $ HOLogic.mk_string "x"`
- `Free("x", _)` in `imp2_com` assign LHS → `HOLogic.mk_string "x"`
- `Free("x", _)` in `imp2_com` call → `HOLogic.mk_string "x"`
- Numeral `n` in `imp2_aexp` → `Const(@{const_name N}, _) $ HOLogic.mk_number @{typ int} n`
- `true`/`false` → `Const(@{const_name Bc}, _) $ @{term True}` / `... False`

```isabelle
ML \<open>
fun imp2_aexp_tr (Free (x, _)) =
      Const (@{const_name IMP2_Syntax.V}, @{typ "vname => aexp"}) $
        HOLogic.mk_string x
  | imp2_aexp_tr (Const (@{syntax_const "_imp2_num"}, _) $ n) =
      Const (@{const_name IMP2_Syntax.N}, @{typ "int => aexp"}) $
        HOLogic.dest_number n |> snd |> HOLogic.mk_number @{typ int}
  | imp2_aexp_tr (Const (@{syntax_const "_imp2_plus"}, _) $ a $ b) =
      Const (@{const_name IMP2_Syntax.aexp.Plus}, ...) $ imp2_aexp_tr a $ imp2_aexp_tr b
  (* ... *)

val imp2_tr : term list -> term = fn [com_term] => imp2_com_tr com_term | _ => raise Match

val _ = Theory.setup
  (Sign.add_advanced_trfuns
    ([], [(@{syntax_const "_IMP2"}, imp2_tr)], [], []))
\<close>
```

Full implementation is ~200 lines of ML — small relative to AutoCorrode's Rust parser.

#### Key design decision: variable names

AutoCorrode's Rust uses lexer-level identifiers (`x`, `left`) that are naturally strings in the AST.
IMP2's variable names are HOL `string` values. Inside `IMP ⟦ ... ⟧`:

- bare `x` → parse translation maps `Free("x", _)` to the string literal `''x''`
- this is the same trick AutoCorrode uses: `Free("foo", _)` in a `urust_identifier` position becomes a runtime string

Escape hatch for HOL terms (e.g., a computed variable name): `⟪expr⟫` as in AutoCorrode.

---

## What Already Exists (Use Now, Zero Cost)

`IMP2_Syntax.thy` already defines:

| Write this | Expands to |
|------------|------------|
| `N n`      | `BaseN (AExp.N n)` |
| `V x`      | `BaseN (AExp.V x)` |
| `Bc v`     | `BaseB (BExp.Bc v)` |

The current examples don't use these even though they're already available. This is the zero-effort immediate improvement regardless of which tier is chosen.

---

## Symbol Safety

`IMP2_Proc` imports `HOL-IMP.Star` (transitive closure), not `HOL-IMP.Com`. HOL-IMP's notation for its own `com` type (`::=`, `;;`, `IF...THEN...ELSE`, `WHILE...DO`) is **never in scope** in any of our sessions. All Tier 1 symbols are free to use.

If a future theory imports `HOL-IMP.Com` directly alongside `IMP2_Proc`, Isabelle disambiguates by type. A `:: "IMP2_Proc.com"` annotation on the definition suffices. Fall back to subscript forms (`::=\<^sub>p`, `;;\<^sub>p`) only if warnings surface.

---

## What Not to Change

| Location | Reason |
|----------|--------|
| `fun to_imp2_com` equations (`IMP2_Bridge.thy`) | Pattern-match heads require constructors, not notation |
| `inductive pstep` rule bodies (`IMP2_Proc.thy`) | Same |
| CFG compilation in `IMP2_Proc_to_CFG.thy` | Pattern-matching throughout |
| `loop_cfg_edges` proofs using `EA_Assign`/`EA_Assume` | CFG edge actions, not `com` constructors |

---

## Recommended Path

1. **Now:** Apply Tier 1 notation + use existing `N`/`V`/`Bc` abbreviations in all example files.
   One Isabelle PR, ~30 lines.

2. **When examples grow:** Tier 2 (`IMP { ... }` block) gives structured syntax without ML overhead.

3. **If a paper or tutorial audience needs it:** Tier 3 quotation bracket gives the full AutoCorrode experience. The IMP2 language is small enough (~10 constructs) that the ML parser is a few hundred lines — a manageable afternoon project.

---

## Migration Checklist (Tier 1)

- [x] Replace `BaseN (AExp.N _)` → `N _`, `BaseB (BExp.Bc _)` → `Bc _`, `BaseN (AExp.V _)` → `V _` in both example files
- [x] Add `notation` block to `IMP2_Proc.thy` after `datatype com`
- [x] Update example `definition` sites to use the new notation
- [x] I/Q diagnostics clean on `IMP2_Proc.thy` and both example theories
- [x] Final gate: `isabelle build -v -N -d ~/afp/thys -d vendor/td-verification -D . Voblint_Formalization`
