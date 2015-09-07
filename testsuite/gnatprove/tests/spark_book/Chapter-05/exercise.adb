with Ada.Integer_Text_IO; use Ada.Integer_Text_IO;
procedure Exercise is
   type Percent       is delta 0.25 range 0.0 .. 100.0;
   type Percent_Array is array (Integer range <>) of Percent;

   function Num_Below (List  : in Percent_Array;
                       Value : in Percent) return Natural
   -- Returns the number of values in List that are less than Value
      with
         Pre => (for all J in List'First .. List'Last - 1 =>
                     List (J) <= List (J + 1))
   is
      Result : Natural;
      Index  : Integer;
   begin
      Result := 0;
      Index  := List'First;
      loop
         exit when Index > List'Last or else List (Index) >= Value;
         Result := Result + 1;
         Index  := Index + 1;
      end loop;
      return Result;
   end Num_Below;

begin
   Put (Num_Below (List  => (11.2, 23.4, 33.4, 48.6, 51.6, 61.7, 71.5),
                   Value => 50.0));
end Exercise;
