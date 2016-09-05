pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);

package Init_Concurrent with SPARK_Mode is
   function Id (X : Natural) return Natural is (X) with
   Pre => X > 0;

   protected Wrong_Init is
      function Get_V return Natural;
      procedure Set_V (X : Natural);
   private
      V : Natural := Id (0); --@PRECONDITION:FAIL
   end;
end Init_Concurrent;
