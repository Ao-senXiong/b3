# Motivation

Authoring an automated program verification is a complex task that can be broken up into two
major components with separate concerns. One component is the _front end_, which prescribes the
proof obligations for any given source program. The other component is the _back end_, which
uses algorithms that try to discharge these proof obligations. The front end is concerned
with _what_ the proof obligations are (for the source language at hand), whereas the back end is
concerned with _how_ to discharge the proof obligations. The front end and back end are joined
at an Intermediate Verification Language (IVL). For the front-end author, the IVL becomes a
thinking tool that suggests ways to prescribe the kinds of verification conditions that commonly
arise in a program verifier. For the back-end author, the IVL provides a primitive and precise
foundation upon which to build its algorithms.

The back end makes use of a set of cooperating decision procedures or semi-decision procedures,
each of which is equipped to handle a particular domain (e.g., linear integer arithmetic). Such
decision procedures are provided in off-the-shelf Satisfiability Modulo Theories (SMT) solvers.
The back end works by turning the proof obligations prescribed by a given IVL program into
queries posed to one or several SMT solvers (henceforth referred to as just the _solver_).

In the last 25 years, IVLs have been used effectively in dozens of automated program
verifiers. Widely used IVLs include Boogie, Why3, and Viper. For example, the verifier for the
Dafny programming language has, since its creation in 2008, used the Boogie 2 IVL and
tool. This long experience has developed several patterns of prescribing proof obligations that
are not well supported by Boogie 2.
