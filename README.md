# PSK-NSL final proof

To run, either install EasyCrypt release 2026.06 and the associated SMT
solvers:
- Alt Ergo 2.6
- Z3 4.13

Or use the EasyCrypt docker image.

In the project directory, run

```
docker run -v .:/home/charlie/nsl -it ghcr.io/easycrypt/ec-test-box:r2026.06
```

to enter the test box. Then to compile

```
cd nsl && opam exec -- make check
```

Once you have a setup working, simply run `make`.

## File structure

The `kap1` directory contains the set of source files making up
the proof, the files are:

- `Games.ec` contains the full game descriptions as in Figure 7 of
the paper, and the proofs of the relevant one-sided invariants.

- `Security.ec` contains the game hopping proof and reductions
for proving Theorem 1. The lemma `final` on line 2143 corresponds
directly to this theorem.

- `PRF.ec`, `AKE.ec`, and `Aead.ec` contain the security defintions
described in the preliminaries.

- `KAP1.ec` contains the definition of PSK-NSL protocol.
