with Ada.Float_Text_IO;
procedure Bad_Types is
   Room_Length    : Float;   -- length of room in feet
   Wall_Thickness : Float;   -- thickness of wall in inches
   Total          : Float;   -- in feet
begin
   Ada.Float_Text_IO.Get (Room_Length);
   Ada.Float_Text_IO.Get (Wall_Thickness);
   Total := Room_Length + 2.0 * Wall_Thickness;
   Ada.Float_Text_IO.Put (Item => Total, Fore => 1, Aft  => 2, Exp  => 0);
end Bad_Types;
