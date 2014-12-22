package body Validation
  with SPARK_Mode
is

   procedure Validate_Sequence (A : in Arr_T; Success : in out Boolean) is
   begin

      for Pos in A'Range loop
         if not Is_Valid (A (Pos))
         then
            Success := False;
            exit;
         end if;

         --  Every element encountered so far (including Pos) is valid.
         pragma Loop_Invariant
           (for all K in A'First .. Pos => Is_Valid (A (K)));
      end loop;

   end Validate_Sequence;

end Validation;

