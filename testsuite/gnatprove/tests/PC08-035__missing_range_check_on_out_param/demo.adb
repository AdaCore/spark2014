package body Demo
with SPARK_Mode => On is

   procedure called (a : out range_A) is
   begin
      a := range_a'Last; --@RANGE_CHECK:FAIL
   end called;


   procedure caller (b : out range_B) is
   begin
      -- Since a and b are of disjoint sub range of float, we get a constraint
      -- error. The prover did not report this.
      called (a => b);
   end caller;

end Demo;
