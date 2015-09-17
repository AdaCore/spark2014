package body Unref
  with SPARK_Mode
is
   procedure Nested_Param (X : out Float)
     with Post => X = 1.0
   is
   begin
      X := 1.0;
   end Nested_Param;

   procedure Nested_Inlined (X : out Float) is
   begin
      X := 1.0;
   end Nested_Inlined;

   procedure Local (Y : out Integer) is
      Loc : Float;
      pragma Unreferenced (Loc);
   begin
      Loc := 1.0;
      Nested_Param (Loc);
      Nested_Inlined (Loc);
      Y := 1;
   end Local;
end Unref;
