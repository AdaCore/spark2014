package body Validation
  with SPARK_Mode
is

   procedure Log_Validation_Error is
   begin
      null;
   end Log_Validation_Error;

   procedure Validate_Sequence (A : in Arr_T; Success : in out Boolean) is
   begin

      for Pos in A'Range loop
         if not Is_Valid (A (Pos))
         then
            Success := False;
            Log_Validation_Error;
         end if;

         --  This relaxed loop invariant will be valid even after an invalid
         --  element has been encountered:
         --
         --  *If* invalidity has not yet been flagged, then every element
         --  encountered so far (including Pos) is valid.
         pragma Loop_Invariant (if Success then
           (for all K in A'First .. Pos => Is_Valid (A (K))));
      end loop;

   end Validate_Sequence;

end Validation;

