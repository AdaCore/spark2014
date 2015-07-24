package body With_Iterable with SPARK_Mode is

   procedure Set_To_0 (A : in out Container) is
      First : Cursor_2 := (C => Max + 1, I => 1);
   begin
      A.Content (1) := 0;
      pragma Assert (Has_Element (A, First));
   end Set_To_0;

end With_Iterable;
