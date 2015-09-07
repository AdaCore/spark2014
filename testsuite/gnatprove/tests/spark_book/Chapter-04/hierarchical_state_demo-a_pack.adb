package body Hierarchical_State_Demo.A_Pack
   with Spark_Mode    => On,
        Refined_State => (State => Total)
is
   Total : Natural := 0;

   procedure A_Proc (Test : in out Natural)
      with Refined_Global  => (In_Out => Total),
           Refined_Depends => ((Test  =>+ Total,
                                Total =>+ Test)) is
   begin
      if Total > Natural'Last - Test   then
         Total := abs (Total - Test);
      else
         Total := Total + Test;
      end if;
      Test := Total;
   end A_Proc;
end Hierarchical_State_Demo.A_Pack;
