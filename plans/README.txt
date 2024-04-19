The files in this directory are intended to be used with the --plan option of
telegraph send.

* spark2014.plan:
   identical to the spark2014 preset.
   Build why3 and spark2014 with assertions enabled, run testsuite and acats
* spark2014+gnat.plan:
   identical to the spark2014-ext preset.
   Same as spark2014.plan, but also build gcc and gnsa
* spark2014_only.plan:
   identical to the spark2014 preset, without build of why3
* bench.plan:
   build why3 and spark2014, generate VCs for alt-ergo, z3, cvc5, then generate
   benchmarks with a 10s timeout
