package body Q
is

   pragma SPARK_Mode (On);

   procedure Convert (
                Raw_In : in     T.Input_T;
                Scale  : in     T.Scale_T;
                Value  :    out T.Output_T)
   is
      X : Float;
   begin

      X := Float (Raw_In) / T.S_Scale;

      if X >= T.S_Max then
         X := X - T.S_MSB;
      end if;

      pragma Assert (X in -20.0 .. 20.0);
      X := X / Float (Scale);

      if X >= Float (T.Output_T'Last) then
         Value := T.Output_T'Last;
      elsif X <= Float (T.Output_T'First) then
         Value := T.Output_T'First;
      else
         Value := T.Output_T (X);
      end if;

   end Convert;

end Q;

