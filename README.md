# Grove

Grove is a separation logic library for verifying distributed systems. It is
built as an extension of the Perennial framework, and thus actually lives in the
Perennial repository [here](https://github.com/mit-pdos/perennial). It is
described in [this SOSP'23 paper](https://people.csail.mit.edu/upamanyu/sharma-grove.pdf).

In the Perennial repository, the
[`src/program_proof/vrsm`](https://github.com/mit-pdos/perennial/tree/master/src/program_proof/vrsm)
contains proofs related to the case study built in the SOSP'23 paper.  The Go
source code for this case study can be found
[here](https://github.com/mit-pdos/gokv).
