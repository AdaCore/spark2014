To run the examples, launch the command:

$ gnatprove -P test.gpr -j0

Nothing should be printed as everything is verified. To get the detail of all verifications done, use:

$ gnatprove -P test.gpr -j0 --report=statistics

All proved checks should be reported, along with the provers used to prove it and the maximal time spent per VC (there can be several VCs for a single check).
A summary of the analysis will be generated inside obj/gnatprove.out.
