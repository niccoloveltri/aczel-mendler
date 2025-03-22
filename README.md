# A Terminal Coalgebra Theorem in HoTT

Formalization of Section 7 of the paper ["Terminal Coalgebras and Non-wellfounded Sets in Homotopy Type Theory"](https://arxiv.org/abs/2001.06696).

Directory [code](https://github.com/niccoloveltri/aczel-mendler/tree/main/code) contains a proof of Aczel-Mendler terminal coalgebra theorem in Cubical Agda.  
Directory [code-var](https://github.com/niccoloveltri/aczel-mendler/tree/main/code-var) contains a variant of the proof that works for building the terminal coalgebra of the powerset functor.  

The formalization type-checks with Agda 2.6.2 and the following version of the Cubical library:  
[https://github.com/agda/cubical/tree/dbe0176d3f873b2ec984720215e37c618c811d53](https://github.com/agda/cubical/tree/dbe0176d3f873b2ec984720215e37c618c811d53).

In the paper, all constructions are presented using a single universe U : Type.
In the Agda code, they are universe-polymorphic.