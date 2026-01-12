with Ada.Text_IO;
with Volatile_Package;

procedure Volatile_Uninit with SPARK_Mode => On
is

   type Array_Type is array (Volatile_Package.Index_Type) of Integer;

   Local_Array : constant Array_Type := (others => 15); -- Some arbitrary value

   Local_Index_Variable : Volatile_Package.Index_Type;

   Local_Integer : Integer;

begin
   Local_Index_Variable := Volatile_Package.Volatile_Variable;
   Local_Integer := Local_Array (Local_Index_Variable);
   Ada.Text_IO.Put_Line ("Value of Local_Integer: " & Local_Integer'Image);

   Local_Index_Variable := Volatile_Package.Volatile_Initialized_Variable;
   Local_Integer := Local_Array (Local_Index_Variable);
   Ada.Text_IO.Put_Line ("Value of Local_Integer: " & Local_Integer'Image);

   Local_Index_Variable := Volatile_Package.Volatile_Imported_Variable;
   Local_Integer := Local_Array (Local_Index_Variable);
   Ada.Text_IO.Put_Line ("Value of Local_Integer: " & Local_Integer'Image);
end Volatile_Uninit;
