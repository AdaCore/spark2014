with Ada.Text_IO;          use Ada.Text_IO;
with Ada.Integer_Text_IO;  use Ada.Integer_Text_IO;
procedure Enum_Example is
   --Declaration of three enumeration types
   type Day_Type is (Monday, Tuesday, Wednesday, Thursday,
                     Friday, Saturday, Sunday);
   type Traffic_Light_Color is (Red, Green, Yellow);
   type Pixel_Color         is (Red, Green, Blue, Cyan,
                                Magenta, Yellow, Black, White);

   package Day_IO is new Ada.Text_IO.Enumeration_IO (Day_Type);

   function Next_Day (Day : in Day_Type) return Day_Type is
   begin
      if Day = Day_Type'Last then
         return Day_Type'First;
      else
         return Day_Type'Succ (Day);
      end if;
   end Next_Day;

   Today    : Day_Type;
   Tomorrow : Day_Type;
   Count    : Integer;
begin
   Put_Line ("What day is today?");
   Day_IO.Get (Today);
   Tomorrow := Next_Day (Today);
   Put ("Tomorrow is ");
   Day_IO.Put (Item  => Tomorrow,
               Width => 1,
               Set   => Ada.Text_IO.Lower_Case);
   New_Line;

   if Today > Tomorrow then
      Put_Line ("Today must be Sunday");
   end if;
   New_Line;

   Put_Line ("The week days are ");
   for Day in Day_Type range Monday .. Friday loop
      Day_IO.Put (Day);
      New_Line;
   end loop;
   New_Line (2);

   for Color in Traffic_Light_Color loop
      Put_Line (Traffic_Light_Color'Image (Color));
   end loop;
   New_Line (2);

   Count := 0;
   for Color in Pixel_Color range Red .. Yellow loop
      Count := Count + 1;
   end loop;
   Put (Item => Count, Width => 1);
end Enum_Example;

