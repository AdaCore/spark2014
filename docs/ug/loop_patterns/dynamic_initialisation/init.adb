package body Init
  with SPARK_Mode
is

   procedure Dynamic_Initialize (A : out Arr_T; Init_Val : in Component_T)
   is
   begin
      --  using array aggregate here avoids data flow initialisation issues:
      A := (A'Range => 1);

      for Idx in A'Range loop
         --  precondition is strong enough for overflow and range checks here
         A (Idx) := Init_Val + Idx;

         --  every element so far (including Idx) has been initialized:
         pragma Loop_Invariant
           (for all J in A'First .. Idx => A (J) = Init_Val + J);
      end loop;

   end Dynamic_Initialize;

end Init;
