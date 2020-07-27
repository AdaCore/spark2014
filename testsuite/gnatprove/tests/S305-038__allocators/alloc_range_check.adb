procedure Alloc_Range_Check with SPARK_Mode is

   type My_Integer is new Integer with Default_Value => -1;

   function Id (X : My_Integer) return My_Integer with Pre => True;
   function Id (X : My_Integer) return My_Integer is
   begin
      return X;
   end Id;

   C : constant My_Integer := Id (0);
   subtype My_Natural is My_Integer range C .. My_Integer'Last;
   D : constant My_Natural := C;

   type Int_Ptr is access My_Natural;

   J : My_Integer := -3;
   W : Int_Ptr := new My_Integer; --@RANGE_CHECK:FAIL
   V : Int_Ptr := new My_Integer'(J); --@RANGE_CHECK:FAIL
   X : Int_Ptr := new My_Natural; --@RANGE_CHECK:NONE
   Y : Int_Ptr := new My_Natural'(D); --@RANGE_CHECK:NONE
begin
   null;
end Alloc_Range_Check;
