procedure Main with SPARK_Mode is

   --  Record type with immutable discriminants
   type My_Rec
     (D : Boolean)
   is record
      null;
   end record;

   procedure P is
      Y1 : My_Rec := (D => False);
   begin
      --  Objects of immutable record type are always constrained
      pragma Assert (not Y1'Constrained); --@ASSERT:FAIL
      pragma Assert (Y1'Constrained); --@ASSERT:PASS
   end P;

begin
   P;
end Main;
