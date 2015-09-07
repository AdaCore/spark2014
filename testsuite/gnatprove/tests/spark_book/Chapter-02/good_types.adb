with Ada.Text_IO;
procedure Good_Types is
   -- Declarations of two floating point types
   type Feet   is digits 4 range 0.0 .. 100.0;
   type Inches is digits 3 range 0.0 .. 12.0;

   -- Instantiation of input/output packages for feet and inches
   package Feet_IO is new Ada.Text_IO.Float_IO (Feet);
   package Inch_IO is new Ada.Text_IO.Float_IO (Inches);

   function To_Feet (Item : in Inches) return Feet is
   begin
      return Feet (Item) / 12.0;
   end To_Feet;

   Room_Length    : Feet;
   Wall_Thickness : Inches;
   Total          : Feet;
begin
   Feet_IO.Get (Room_Length);
   Inch_IO.Get (Wall_Thickness);
   Total := Room_Length + 2.0 * To_Feet (Wall_Thickness);
   Feet_IO.Put (Item => Total, Fore => 1, Aft => 1, Exp => 0);
end Good_Types;
