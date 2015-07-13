package Private_Types with SPARK_Mode is
   type Root is tagged private;
   type Root_D (C : Natural) is tagged private;
   C   : constant Root;
   C_D : constant Root_D;
private
   pragma SPARK_Mode (Off);
   type Root is tagged null record;
   type Root_D (C : Natural) is tagged null record;
   C   : constant Root := Root'(null record);
   C_D : constant Root_D := (C => 0);
end Private_Types;
