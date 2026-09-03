---
title: Verifying libcrux AES using hax + Lean
description: A summary of my Master's thesis on formally verifying a real-world cryptographic implementation
slug: master-thesis
date: 2026-06-30
image:
categories:
    - Academic
tags:
math: true
---

After a lot of work, I have finished my Master's thesis at Aarhus University,
under the supervision of [Bas Spitters](https://www.cs.au.dk/~spitters/). This post is a
brief, summary of what I did and why I think it is interesting. If you
want the full details, the code is available in [this GitHub repository](https://github.com/ErVinuelas/aes_hax/).

### The problem

During my previous work with the SSProve framework, I focused on checking the properties
of a given cryptographic construction. That is, we formalized the proofs presented
in the same paper that the construction was explained. 

For my master thesis I wanted to explore a different path, I wanted to build on an
existing real-world implementation and check that the properties we wanted it to have
were actually there. I also wanted to learn more about Lean, since I had only used Rocq
as an interactive theorem prover in previous projects.

Therefore, I talked with the people at [Cryspen](https://cryspen.com/), to see if they had a project in mind
that could suit my interests. I had been following them for a while, since Bas worked with 
them, and I think that what they do as a company is very cool.

They suggested that I could use [Hax](https://github.com/hacspec/hax) and the new [Lean](https://leanprover.github.io/)
backed they had been developing to reason around their [AES](https://github.com/celabshq/libcrux/tree/main/crates/algorithms/aes)
implementation. Even though AES is a simple algorithm, the difficulty of the project
would be dealing with having to work with a software that was being developed
as I was doing the project.

### The two tools, briefly

Before jumping into the example, it helps to know what the two tools do.

[Hax](https://github.com/hacspec/hax) takes idiomatic Rust and produces a *model* of it
in a backend. It already supported F\*, Rocq and SSProve, and the Cryspen team had
started work on a Lean backend, which is the one I used. One detail worth mentioning early:
because any Rust computation can panic or diverge, Hax wraps every function in a monad
(called `RustM`) that accounts for those outcomes. So a humble `fn f(x: u32) -> u32` does
not come out as a function returning `u32`, but as one returning `RustM u32`. The generated
code is not meant to be pretty; it is meant to faithfully mirror what the Rust does.

[Lean](https://leanprover.github.io/) is both a functional programming language and an
interactive theorem prover. I relied on two of its features in particular. The first is its
imperative `do`-notation together with support for [Hoare triples](https://en.wikipedia.org/wiki/Hoare_logic),
which let me state "if this precondition holds, running the program gives a result
satisfying this postcondition" and discharge it with the `mvcgen` tactic. The second is
`bv_decide`, a tactic that closes goals about fixed-width bitvectors by calling out to a SAT
solver. Both turned out to be a good fit for low-level code that is mostly bit tweakering.

### The workflow

For each function I wanted to verify, I ended up repeating the same four steps:

1. **Pick** one of the core functions from the libcrux AES implementation.
2. **Translate** it into a Lean model with Hax.
3. **Specify** what the function is supposed to do, writing a Lean function that stays as
   close as possible to the textbook description of AES.
4. **Prove** a theorem that ties the generated model to that specification.

That is the whole loop, and the rest of this post is really just that loop applied once, to
MixColumns. Happily, everything I looked at did match the specification.

### A worked example: MixColumns

AES works on a 128-bit block laid out as a 4×4 matrix of bytes, called the *state*. Each
round pushes the state through a handful of transformations, one of which is MixColumns.
It is a nice example to follow because it is small enough to describe in a paragraph, yet it
touches almost everything that made the project interesting.

#### What MixColumns is supposed to do

Each column of the state is multiplied by a fixed matrix in \(GF(2^8)\):

$$
\begin{bmatrix} s'_{0,c} \\ s'_{1,c} \\ s'_{2,c} \\ s'_{3,c} \end{bmatrix} =
\begin{bmatrix}
02 & 03 & 01 & 01 \\
01 & 02 & 03 & 01 \\
01 & 01 & 02 & 03 \\
03 & 01 & 01 & 02
\end{bmatrix}
\begin{bmatrix} s_{0,c} \\ s_{1,c} \\ s_{2,c} \\ s_{3,c} \end{bmatrix}
$$

The catch is that this is not ordinary arithmetic. The entries are bytes interpreted as
elements of the Galois field \(GF(2^8)\), so "\(+\)" is a bitwise XOR and "\(\cdot\)" is
carry-less polynomial multiplication reduced modulo a fixed irreducible polynomial. In
practice the only multipliers that appear here are \(02\) and \(03\), and multiplying by
\(02\) is just a shift with a conditional XOR (the operation usually called `xtime`). This
is exactly why the field arithmetic has to be built up first: before I could say anything
about MixColumns, Lean needed to understand what \(0x02 \cdot s\) even means.

#### How libcrux actually implements it

If the implementation kept the state as a 4×4 grid of bytes and multiplied it by that
matrix, there would be almost nothing to verify. But libcrux is written to be fast and to
run in constant time, so it *bitslices* the state. Instead of
sixteen bytes, the state is stored as an array of eight `u16` values, where each `u16`
holds one "bit-plane", the collection of all the *i*-th bits of the original bytes. The
byte-level matrix from above is gone; what is left is a sequence of shifts, masks and XORs
across those planes.

The upside is a fast, branch-free implementation. The downside is that if you are not versed
in this kind of techniques, the Rust does not visibly compute MixColumns at all, and you essentially
have to trust the author. Closing that gap between "looks nothing like the spec" and
"provably *is* the spec" is the whole reason a project like this is worth doing.

#### Modelling it in Lean

There were two pieces to write. The first is the field arithmetic. I represented an element
of \(GF(2^8)\) as an 8-bit vector and defined multiplication in the usual way, on top of the
`xtime` operation:

```lean
abbrev GF8 := BitVec 8

def polyRed : GF8 := 0x1B#8

def xtime (a : GF8) : GF8 :=
  let shifted := a <<< 1#8
  if a.getLsbD 7 then shifted ^^^ polyRed else shifted

def mulStep (b : GF8) (state : GF8 × GF8) (bitIdx : Nat) : GF8 × GF8 :=
  let (acc, cur_a) := state
  (if b.getLsbD bitIdx then acc ^^^ cur_a else acc, xtime cur_a)

def mul (a b : GF8) : GF8 :=
  let bitIndices := List.range 8
  (bitIndices.foldl (mulStep b) (zero, a)).1
```

I also had to prove a few small lemmas that rewrite this definition into a shape
`bv_decide` is happy with, for instance that multiplying by `0x02` is exactly `xtime`. These
are not exciting on their own, but MixColumns needs multiplication by `0x02` and `0x03`, so
this groundwork is what makes the interesting proof possible.

The second piece is the specification itself. Here I deliberately tried to make it read like
the matrix a reader already knows, rather than like the bitsliced code:

```lean
def mix_columns_state_spec (st : Vector u16 8) : Vector u16 8 :=
  (4 : Nat).fold (init := zero_array) fun group_indx _ res =>
    let index := group_indx * 4
    let s_0 := get_elem st index
    let s_1 := get_elem st (index + 1)
    let s_2 := get_elem st (index + 2)
    let s_3 := get_elem st (index + 3)
    -- the + and * below are the GF(2^8) operations
    let s_0' := 0x02 * s_0 + 0x03 * s_1 + s_2 + s_3
    let s_1' := 0x02 * s_1 + 0x03 * s_2 + s_3 + s_0
    let s_2' := 0x02 * s_2 + 0x03 * s_3 + s_0 + s_1
    let s_3' := 0x02 * s_3 + 0x03 * s_0 + s_1 + s_2
    let set_0 := set_elem res index s_0'
    let set_1 := set_elem set_0 (index + 1) s_1'
    let set_2 := set_elem set_1 (index + 2) s_2'
    set_elem set_2 (index + 3) s_3'
```

The four lines in the middle are essentially the matrix written out row by row. The helper
functions `get_elem` and `set_elem` hide the bitslicing, so the specification recovers the
original 4×4 view of the state. That readability was a goal in itself: a specification is
only useful if a human can look at it and agree that it really is AES.

#### Proving the theorem

With both sides in hand, the theorem to prove is simply that running the model produces the
same state as the specification. Written as a Hoare triple it looks like this:

```lean
theorem mix_columns_state_correct (st : RustArray u16 8) :
  {| ⌜ true ⌝ |}
  mix_columns_state st
  {| ⇓ ⟨ res ⟩ =>
    ⌜ res = mix_columns_state_spec st ⌝ |}
```

The precondition is trivial and the postcondition says "the result equals the readable
spec". The proof itself is mostly two tactics. First `mvcgen` unfolds the monadic `do`-program
into a set of verification conditions. Then `bv_decide` discharges the bitvector goals by
handing them to a SAT solver, which is where all the shift/mask/XOR reasoning about the
bitsliced representation actually gets checked.

That is the tidy version. In reality the conditions `mvcgen` generated for these bitsliced
functions were huge, spanning several screens, and Lean would sometimes run out of memory
just trying to display them. I ended up writing a few helper tactics to rename and
substitute the hypotheses in a systematic way, which was as much about keeping Lean alive as
about keeping the proof readable.

### What was hard

MixColumns went relatively smoothly, but it is a fair representative of the friction I ran
into across the project. A few things stood out.

The biggest one was that the Lean backend was still young. Some Rust operations had no
translation yet, and some library functions were simply missing, for example the operation
that updates a value at an index in a slice, or the `UInt128` type, which Lean did not offer
but the libcrux code uses. Many of these I could work around by adding the missing pieces
myself; others needed a hand from the Cryspen team, who were very helpful and generous with their time.
Loop invariants were another gap: expressing them in the Rust source was not yet fully supported, so
I had to fall back on embedding Lean code, which is workable but clunky.

`bv_decide` was a similar story. It is excellent on plain bitvectors, but as soon as the
goal mixes in indices or other types it can get stuck, and when it does the failure is hard
to debug. Combined with the enormous goals `mvcgen` produced, and the limited control Lean
gives you over how much of a proof it processes at once, a fair amount of my effort went
into simply managing the size of things rather than the mathematics.

Finally, there is a genuine tension I do not think has a clean answer: the closer a
specification sits to the code, the easier it is to link the two, but the harder it is to
read; abstract too far in the other direction and it becomes hard to connect back to the
implementation. I tried to find a reasonable middle ground, but where that middle sits
feels fairly personal.

### Wrapping up

By the end I was able to link the libcrux portable AES-128 and AES-256 implementations to a
mathematical specification that someone who knows AES could actually read and
trust. As far as I know this was the first time Hax and Lean had been used together on a
complete cipher, so I mostly see the result as evidence that the approach is viable, not as
a finished or polished piece of infrastructure. The tools will keep changing, and some of
the rough edges above are already being smoothed out.

There is plenty left to do. I only tackled the AES core, not the surrounding AES-GCM
protocol, and libcrux has many other primitives waiting for the same treatment, SHA3 would
be a natural next target. On the tooling side, extending `bv_decide` to the cases where it
currently gets stuck would remove a lot of the pain, and it would be interesting to see how
far AI-assisted proof generation can help with the more tedious parts.

Thanks to [Bas Spitters](https://www.cs.au.dk/~spitters/) for supervising, and to the
[Cryspen](https://cryspen.com/) team for suggesting the project and patiently answering my
questions along the way. If you want the details, everything is in
[the repository](https://github.com/ErVinuelas/aes_hax/).

