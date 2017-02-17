package body Sorters_Not_Global is

   -- Swaps the values of two components in the array Values.
   procedure Swap (X      : in Index_Type;
                   Y      : in Index_Type;
                   Values : in out Array_Type)
   with
     Depends => (Values => (Values, X, Y)),
     Pre     => X /= Y,
     Post    =>
       Values (X) = Values'Old (Y) and
       Values (Y) = Values'Old (X) and
       (for all J in Index_Type range Values'Range =>
         (if (J /= X and then J /= Y) then Values (J) = Values'Old (J)));

   procedure Swap (X      : in Index_Type;
                   Y      : in Index_Type;
                   Values : in out Array_Type)
   is
      Temp : Integer;
   begin
      Temp       := Values (X);
      Values (X) := Values (Y);
      Values (Y) := Temp;
   end Swap;

   -- Finds the smallest element in the remaining unsorted data.
   function Index_Of_Minimum (Starting_At : in Index_Type;
                              Limit       : in Index_Type;
                              Values      : in Array_Type) return Index_Type
   with
     Pre => Starting_At <= Limit,
     Post =>
       Starting_At <= Index_Of_Minimum'Result and
       Index_Of_Minimum'Result <= Limit       and
       (for all J in Index_Type range Starting_At .. Limit =>
            Values (Index_Of_Minimum'Result) <= Values (J));

   function Index_Of_Minimum (Starting_At : in Index_Type;
                              Limit       : in Index_Type;
                              Values      : in Array_Type) return Index_Type
   is
      Min : Index_Type;
   begin
      Min := Starting_At;
      for Index in Index_Type range Starting_At + 1 .. Limit loop
         pragma Loop_Invariant
           (Limit = Limit'Loop_Entry and then
            Starting_At <= Min and then Min <= Limit and then
            (for all J in Index_Type range Starting_At .. Index - 1 =>
               Values (Min) <= Values (J)));

         if Values (Index) < Values (Min) then
            Min := Index;
         end if;
      end loop;
      return Min;
   end Index_Of_Minimum;

   procedure Selection_Sort (Values : in out Array_Type;
                             Limit  : in Index_Type) is
      Smallest : Index_Type;
   begin -- Selection_Sort
      for Current in Index_Type range Values'First .. Limit loop
         Smallest := Index_Of_Minimum (Starting_At => Current,
                                       Limit       => Limit,
                                       Values      => Values);
         if Smallest /= Current then
            Swap (X      => Current,
                  Y      => Smallest,
                  Values => Values);
         end if;

         pragma Loop_Invariant
           ((for all J in Index_Type range Values'First .. Current - 1 =>
               Values (J) <= Values (J + 1)) and then
            (for all J in Index_Type range Current .. Limit =>
               Values (Current) <= Values (J)));
      end loop;
   end Selection_Sort;

end Sorters_Not_Global;
