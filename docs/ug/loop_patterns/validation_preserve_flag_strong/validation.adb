package body Validation
  with SPARK_Mode
is

   procedure Validate_Sequence (A : in Arr_T; Success : in out Boolean) is
   begin

      for Pos in A'Range loop
         if not Is_Valid (A (Pos))
         then
            Success := False;
         end if;

         --  The loop invariant defines exactly what the truth value of the
         --  flag (Success) should be at an arbitrary looop iteration.
         pragma Loop_Invariant
           (Success = (Success'Loop_Entry and
                       (for all K in A'First .. Pos => Is_Valid (A (K)))));
      end loop;

   end Validate_Sequence;

end Validation;


