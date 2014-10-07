package body Exclude_Unit_Body with
  SPARK_Mode => Off
is
   --  this package body is not analyzed

   Value : T := new Integer;

   function Get_Value return Integer is
   begin
      return Value.all;
   end Get_Value;

   procedure Set_Value (V : Integer) is
   begin
      Value.all := V;
   end Set_Value;

end Exclude_Unit_Body;
