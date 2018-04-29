package body Competition with
   SPARK_Mode
is

   ------------
   -- Unique --
   ------------

   function Unique (Input : List) return List is
      Result : List (Input'Range) := (others => 0);
      --  Reason for this test: No references to result in CE line 12.
      Count  : Zero_Index := Result'First - 1;
   begin
      return Result (Result'First .. Count);
   end Unique;

end Competition;
