# A Terminal Coalgebra Theorem in HoTT

Formalization of Section 6 of the paper ["Terminal Coalgebras and Non-wellfounded Sets in Homotopy Type Theory"](https://arxiv.org/abs/2001.06696).

Directory [code](https://github.com/niccoloveltri/aczel-mendler/tree/main/code) contains a proof of Aczel-Mendler terminal coalgebra theorem in Cubical Agda.  
Directory [code-var](https://github.com/niccoloveltri/aczel-mendler/tree/main/code-var) contains a variant of the proof that works for building the terminal coalgebra of the powerset functor.  

The formalization type-checks with Agda 2.8.0 and Cubical library version 0.9.

In the paper, all constructions are presented using a single universe U : Type.
In the Agda code, they are universe-polymorphic.

## Compiling with Nix

This repo has been packaged as a Nix flake. Thus, if you have Nix installed (and
have allowed experimental features) you can compile the Agda code in the repo by
first running:

```bash
$ nix develop
```

This will create a shell that contains the Agda and cubical versions needed to
compile the code. (Note: this command may take a while to execute the first time
as it needs to build the cubical library. But subsequent runs should be much
faster as Nix will reuse the build files.)

You can then type check the Agda code as usual inside this new shell:

```bash
$ agda <agda-file-to-type-check>
```
