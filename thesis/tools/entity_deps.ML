(*
 Emit
 the
 statement-level
 dependency
 graph
 of
 the
 formalization
 as
 JSON.
 An
 edge
 X
 ->
 Y
 means
 Y
 occurs
 in
 what
 X
 states:
 the
 proposition
 of
 a
 fact,
 the
 defining
 specification
 of
 a
 constant
 or
 type,
 the
 parents
 and
 predicate
 of
 a
 locale.
 Proofs
 are
 not
 followed ; a lemma used only inside
 a
 proof
 is
 not
 something
 a
 reader
 needs
 before
 the
 statement.
 The
 edges
 come
 from
 the
 kernel,
 not
 from
 the
 source
 text:
 constant
 specifications
 from
 `Theory.defs_of`
 (the table Isabelle keeps to check definitions for cycles)
 ,
 statements
 from
 the
 facts'
 propositions.
 Names
 therefore
 arrive
 fully
 qualified
 and
 with
 notation
 and
 locale
 syntax
 already
 resolved.
 Type
 synonyms
 and
 abbreviations
 are
 expanded
 inside
 propositions,
 so
 a
 statement
 about
 `store`
 depends
 on
 what
 `store`
 expands
 to ; the synonym's own node keeps the edge to its expansion.
 Only
 declarations
 from
 theories
 whose
 session
 name
 starts
 with
 one
 of
 the
 given
 prefixes
 become
 nodes.
 Edges
 into
 other
 theories
 are
 kept
 so
 the
 reader
 can
 see
 them,
 but
 they
 are
 not
 expanded.
 *)

signature

ENTITY_DEPS

=

sig

val

json:

string

list

->

theory

->

string

end

;

structure

Entity_Deps:

ENTITY_DEPS

=

struct

fun

owned_theories

prefixes

thy

=

(thy :: Theory.ancestors_of thy)

|>

filter

(fn
 t
 =>
 let
 val
 q
 =
 Long_Name.qualifier
 (Context.theory_long_name t)
 in
 exists
 (fn p => String.isPrefix p q)
 prefixes
 end)

|>

map

Context.theory_base_name

;

fun

owner

name

=

hd

(Long_Name.explode name)

;

fun

add_tycons

(Type
 (c, Ts))

=

insert

(op =)

c

#>

fold

add_tycons

Ts

|

add_tycons

_

=

I

;

fun

term_deps

t

=

map

(pair "const")

(Term.add_const_names t [])

@

map

(pair "type")

(Term.fold_types add_tycons t [])

;

fun

typ_deps

T

=

map

(pair "type")

(add_tycons T [])

;

(*
 Only
 the
 generic
 specification:
 an
 overloaded
 constant
 also
 carries
 one
 specification
 per
 instance,
 which
 says
 nothing
 about
 its
 statement.
 *)

fun

spec_deps

thy

item

=

Defs.specifications_of

(Theory.defs_of thy)

item

|>

filter

(Defs.plain_args o #lhs)

|>

maps

#rhs

|>

map

(fn
 ((Defs.Const, c)
  ,
  _)
 =>
 ("const" , c)
 |
 ((Defs.Type, c)
  ,
  _)
 =>
 ("type" , c))

;

(* A record `R` declares its extension type as `R.R_ext`. *)

fun

record_deps

thy

name

=

if

not

(String.isSuffix "_ext" name)

then

[]

else

(case
 Record.get_info
 thy
 (Long_Name.qualifier name)
 of
 SOME
 {fields,
 parent,
 ...}
 =>
 maps
 (fn
  (f, T)
  =>
  ("const" , f)
  ::
  typ_deps
  T)
 fields
 @
 (case
  parent
  of
  SOME
  (_, p)
  =>
  [
  ("type" , p ^ "." ^ Long_Name.base_name p ^ "_ext")
  ]
  |
  NONE
  =>
  [])
 |
 NONE
 =>
 [])

;

(*
 A
 datatype's
 typedef
 goes
 through
 BNF
 internals ; its constructors say what
 a
 reader
 needs.
 Other
 logical
 types
 fall
 back
 to
 their
 specification.
 *)

fun

logical_type_deps

thy

ctxt

name

=

(case
 Ctr_Sugar.ctr_sugar_of
 ctxt
 name
 of
 SOME
 {ctrs,
 ...}
 =>
 maps
 (typ_deps o fastype_of)
 ctrs
 |
 NONE
 =>
 spec_deps
 thy
 (Defs.Type, name)
 @
 record_deps
 thy
 name)

;

fun

quote_json

s

=

"\""

^

String.translate

(fn # "\"" => "\\\"" | # "\\" => "\\\\" | c => String.str c)

s

^

"\""

;

fun

node_json

(kind, name, deps)

=

let

val

deps'

=

distinct

(op =)

deps

|>

filter_out

(fn
 d
 =>
 d
 =
 (kind, name))

;

val

dep_strs

=

map

(fn
 (k, n)
 =>
 quote_json
 (k ^ ":" ^ n))

deps'

;

in

"  "

^

quote_json

(kind ^ ":" ^ name)

^

": {\"kind\": "

^

quote_json

kind

^

", \"theory\": "

^

quote_json

(owner name)

^

", \"deps\": ["

^

commas

dep_strs

^

"]}"

end

;

fun

json

prefixes

thy

=

let

val

ctxt

=

Proof_Context.init_global

thy

;

val

theories

=

owned_theories

prefixes

thy

;

fun

ours

name

=

member

(op =)

theories

(owner name)

;

val

facts

=

Facts.dest_static

false

[]

(Global_Theory.facts_of thy)

|>

filter

(ours o fst)

|>

map

(fn
 (name, thms)
 =>
 ("thm"
  ,
  name,
  maps
  (term_deps o Thm.prop_of)
  thms))

;

val

consts

=

#constants

(Consts.dest
 (Sign.consts_of thy))

|>

filter

(ours o fst)

|>

map

(fn
 (name,
  (T, abbrev))
 =>
 ("const"
  ,
  name,
  typ_deps
  T
  @
  (case abbrev of SOME rhs => term_deps rhs | NONE => [])
  @
  spec_deps
  thy
  (Defs.Const, name)))

;

val

types

=

Name_Space.fold_table

(fn
 (name, decl)
 =>
 fn
 acc
 =>
 if
 not
 (ours name)
 then
 acc
 else
 (case
  decl
  of
  Type.Abbreviation
  (_, rhs, _)
  =>
  ("type" , name, typ_deps rhs)
  ::
  acc
  |
  Type.Logical_Type
  _
  =>
  ("type" , name, logical_type_deps thy ctxt name)
  ::
  acc
  |
  Type.Nonterminal
  =>
  acc))

(#types
 (Type.rep_tsig
  (Sign.tsig_of thy)))

[]

;

val

locales

=

Locale.pretty_locale_deps

thy

|>

filter

(ours o #name)

|>

map

(fn
 {name,
 parents,
 ...}
 =>
 ("locale"
  ,
  name,
  map
  (pair "locale")
  parents
  @
  spec_deps
  thy
  (Defs.Const, name)
  @
  spec_deps
  thy
  (Defs.Const, name ^ "_axioms")))

;

in

"{\n"

^

space_implode

",\n"

(map
 node_json
 (facts @ consts @ types @ locales))

^

"\n}\n"

end

;

end

;
