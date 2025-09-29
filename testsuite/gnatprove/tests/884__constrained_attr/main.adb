procedure Main with SPARK_Mode is

   --  Record type with immutable discriminants
   type My_Rec
     (D : Boolean)
   is record
      null;
   end record;

   Y : My_Rec := (D => False);
   Z : constant My_Rec := (D => False);
   --  Objects of immutable record type are always constrained

   pragma Assert (Y'Constrained); --@ASSERT:PASS
   pragma Assert (Z'Constrained); --@ASSERT:PASS

begin
   null;
end Main;
