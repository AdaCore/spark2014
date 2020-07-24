package Exclude_Unit_Body with
  SPARK_Mode => On
is

   type T is private;

   function Get_Value return Integer;

   procedure Set_Value (V : Integer) with
     Post => Get_Value = V;

private
   pragma SPARK_Mode (Off);

   --  the private part of the package spec is not analyzed

   type T is access Integer;
end Exclude_Unit_Body;
