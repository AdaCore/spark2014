procedure Rename_Aggregate with SPARK_Mode is

   type Cursor is range 0 .. 100;
   subtype Valid_Cursor is Cursor range 1 .. 100;

   type Nat_Array is array (Valid_Cursor) of Natural;

   A : Nat_Array := (others => 0);
   B : Nat_Array renames Nat_Array'(others => A (1));
begin
   A (1) := 1;
   for E of B loop
      pragma Assert (E = 1);--@ASSERT:FAIL
   end loop;
end Rename_Aggregate;
