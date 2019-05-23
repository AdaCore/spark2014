pragma SPARK_Mode;
package body No_Optim is
   Status : Boolean;

   procedure Handle (V : Mult_Bit_Boolean) is
      Ret_Val : Mult_Bit_Boolean := V with Volatile, No_Caching; -- Need Volatile to prevent compiler optimization
   begin
      if (Ret_Val = NV_TRUE) then
         pragma Assert (Ret_Val = NV_TRUE);
         Do_Something;
      elsif (Ret_Val = NV_FALSE) then
         pragma Assert (Ret_Val = NV_FALSE);
         Do_Something_Else;
      else
         null;
         -- Fault inject detected. Take punitive action
      end if;
   end Handle;

   procedure Do_Something is
   begin
      Status := True;
   end Do_Something;

   procedure Do_Something_Else is
   begin
      Status := False;
   end Do_Something_Else;

end No_Optim;
