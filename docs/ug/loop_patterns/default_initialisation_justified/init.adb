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
         pragma Annotate (GNATprove, False_Positive,
                          "might not be initialized",
                          "A is initialized until and including Idx, so A(J) OK here");
      end loop;

   end Default_Initialize;

end Init;
