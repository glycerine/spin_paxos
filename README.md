spin_paxos
==========

This repository contains extracted and updated
Promela models (for running on the Spin model
checker https://spinroot.com/ ) from the
2014 paper: "Model Checking Paxos in Spin"
by Giorgio Delzanno, Michele Tatarek, and Riccardo Traverso

https://arxiv.org/pdf/1408.5962

The Promela language evolved a little in the
last 11 years, and so I've updated the models 
in small ways, and fixed a couple
of bugs that needed fixing. The pdf linked
above and the code shown in the markdown
version in the papers/ directory reflects the original,
not-updated Promela code. The updated
code is in these two files:

The unoptimized model from the paper is in zpaxminimal.pml.

The optimized model is in optimized.pml.

The included makefile shows how to do a model-checking run.

------------

repository owner: Jason E. Aten, Ph.D.
