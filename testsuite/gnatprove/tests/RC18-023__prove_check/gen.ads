generic
   H: Integer;

package Gen with SPARK_Mode is
   --  ??? Doing prove check --prover=coq here launches 7 coqide
   pragma Assert (H < 0);

end Gen;
