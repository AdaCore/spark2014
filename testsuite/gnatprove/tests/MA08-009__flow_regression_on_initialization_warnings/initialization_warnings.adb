package body Initialization_Warnings
  with SPARK_Mode
is
   procedure Init_Arr_Warn (An_Arr : out Array_T) is
   begin
      for I in 1 .. 9 loop
         An_Arr (I) := I;
      end loop;
   end Init_Arr_Warn;

   procedure Init_Arr_Warn_2 (An_Arr : out Array_T; X : out Integer) is
   begin
      for I in 1 .. 9 loop
         An_Arr (I) := I;
      end loop;
      --  The following read is OK, but requires value-dependent flow analysis
      X := An_Arr (5);  --  @INITIALIZED:CHECK
   end Init_Arr_Warn_2;

   procedure Init_Arr_Warn_3 is
   begin
      for I in 1 .. 9 loop
         A (I) := I;  --  This should be a warning.
      end loop;
   end Init_Arr_Warn_3;

   procedure Init_Arr_Warn_4 is
   begin
      for I in 1 .. 9 loop
         A (I) := I;  --  This should be a warning.
      end loop;

      V := A (5);  --  The above warning should be raised here.
   end Init_Arr_Warn_4;
end Initialization_Warnings;
