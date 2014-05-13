procedure Repr
is

   type Array_Type is array (Positive range <>) of Integer;

   function Index_Of_Minimum (Unsorted : in Array_Type)
                              return Positive
     is (3);

   procedure Selection_Sort (Values : in out Array_Type)
   with
      Global => null
   is
      Smallest : Positive;
   begin
      Smallest := Index_Of_Minimum (Values (5 .. Values'Last));
   end Selection_Sort;

begin
   null;
end Repr;
