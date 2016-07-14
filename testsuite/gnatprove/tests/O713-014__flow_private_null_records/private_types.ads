package Private_Types is

   type Root is tagged private;
   type Root_D (C : Natural) is tagged private;
   C   : constant Root;
   C_D : constant Root_D;

   type Non_Tagged (C : Natural) is private;
   C_NT : constant Non_Tagged;

private

   pragma SPARK_Mode (Off);

   type Root is tagged null record;
   type Root_D (C : Natural) is tagged null record;
   C   : constant Root := Root'(null record);
   C_D : constant Root_D := (C => 0);

   type Non_Tagged (C : Natural) is null record;
   C_NT : constant Non_Tagged := Non_Tagged'(C => 0);

end Private_Types;
