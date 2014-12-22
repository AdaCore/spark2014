package body Init
  with SPARK_Mode
is
   procedure Default_Initialize (A : out Arr_T; Init_Val : in Component_T)
   is
   begin

      for Idx in A'Range loop
         A (Idx) := Init_Val;

         --  every element so far (including Idx) has been initialized:
         pragma Loop_Invariant
           (for all J in A'First .. Idx => A (J) = Init_Val);
      end loop;

   end Default_Initialize;

end Init;
