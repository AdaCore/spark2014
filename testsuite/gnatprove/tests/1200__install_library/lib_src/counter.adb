package body Counter
  with SPARK_Mode
is

   The_Count : Natural := 0;
   --  Hidden state of the library, touched by the subprograms below

   ----------
   -- Bump --
   ----------

   procedure Bump (Amount : Natural) is
   begin
      if The_Count <= Natural'Last - Amount then
         The_Count := The_Count + Amount;
      end if;
   end Bump;

   -----------
   -- Value --
   -----------

   function Value return Natural
   is (The_Count);

end Counter;
