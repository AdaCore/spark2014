package body Formal_Cont with Spark_Mode is

   -- NONRETURNING CASE
   function My_Equal_01 (A, B : Integer) return Boolean
   is
      Result : Boolean := False;
   begin
      while True loop
         Result := (A = B);
      end loop;
      return Result;
   end My_Equal_01;

   procedure Test_01 is
      L : New_Set_01.Set;
   begin
      if New_Set_01.Is_Empty (L) then
         null;
      end if;
   end Test_01;

   -- RETURNING CASE
   function My_Equal_02 (A, B : Integer) return Boolean is (A = B);

   procedure Test_02 is
      L : New_Set_02.Set;
   begin
      if New_Set_02.Is_Empty (L) then
         null;
      end if;
   end Test_02;

end Formal_Cont;
