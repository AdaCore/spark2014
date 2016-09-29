package body Atom2 with SPARK_Mode is

   function Get_Data return Integer is
   begin
      return Data;
   end Get_Data;

   function Get_Data_Plus_One return Integer is
      Tmp : constant Integer := Data;
   begin
      return Tmp + 1;
   end Get_Data_Plus_One;

end Atom2;
