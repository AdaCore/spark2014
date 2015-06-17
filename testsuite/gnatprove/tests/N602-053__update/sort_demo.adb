pragma SPARK_Mode (Off);
with Ada.Text_IO;
with Ada.Integer_Text_IO;
with Sorters;
procedure Sort_Demo is

   Max : constant Integer := 50;
   subtype Index_Type is Integer range 1 .. Max;
   subtype Count_Type is Integer range 0 .. Max;
   subtype My_Array_Type is Sorters.Array_Type (Index_Type);

   List  : My_Array_Type;  -- A list of integers
   Count : Count_Type;     -- Number of values in List
   Value : Integer;        -- One input value

begin
   Ada.Text_IO.Put_Line (Item => "Enter up to 50 integers, enter 0 to end");
   Count := 0;  -- Initially, there are no numbers in List
   loop -- Each iteration, get one number
      Ada.Integer_Text_IO.Get (Item => Value);
      exit when Value = 0;     -- Exit loop on sentinel value
      Count := Count + 1;
      List (Count) := Value;   -- Put Value into the array List
   end loop;

   -- Sort the first Count values in the array List
   Sorters.Selection_Sort (Values => List (1 .. Count));

   Ada.Text_IO.Put_Line (Item => "Here are the sorted numbers");
   for J in 1 .. Count loop
      Ada.Integer_Text_IO.Put (Item  => List (J),
                               Width => 8);
      Ada.Text_IO.New_Line;
   end loop;
end Sort_Demo;
