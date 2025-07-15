procedure Main with SPARK_Mode is

   --  Record type with immutable discriminants
   type My_Rec
     (D : Boolean)
   is record
      null;
   end record;

   Y1 : My_Rec := (D => False);
   --  Objects of immutable record type are always constrained

   pragma Assert (Y1'Constrained); --@ASSERT:PASS

begin
   null;
end Main;
