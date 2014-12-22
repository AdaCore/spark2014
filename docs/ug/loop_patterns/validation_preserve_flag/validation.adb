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

         --  Note here the use of 'Loop_Entry to keep the previously
         --  flagged alarm:
         pragma Loop_Invariant
           ((if Success then
           (for all K in A'First .. Pos => Is_Valid (A (K)))) and
           (if not Success'Loop_Entry then not Success));
      end loop;

   end Validate_Sequence;

end Validation;







