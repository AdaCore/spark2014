package body Loopframe with
  SPARK_Mode
is

   function Get return Idx is
      V : Idx := 0;
   begin
      for X in Valid_Idx loop
         if A (X) then
            V := X;
            exit;
         end if;
--         pragma Loop_Invariant (V = 0);
      end loop;
      return V;
   end Get;

end Loopframe;
