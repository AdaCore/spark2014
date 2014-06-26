package body Sort with SPARK_Mode
is

   -----------------------------------------------------------------------------
   procedure Swap (Values : in out Nat_Array;
                   X      : in     Index;
                   Y      : in     Index)
   with
      Pre  => (X in Values'Range and then
               Y in Values'Range and then
               X /= Y),
      Post => Is_Perm (Values'Old, Values)
   is
      Temp : Natural;
   begin
      Temp       := Values (X);
      Values (X) := Values (Y);
      Values (Y) := Temp;
   end Swap;

   -- Finds the index of the smallest element in the array
   function Index_Of_Minimum (Values : in Nat_Array) return Index
     with
       Pre  => Values'Length > 0,
       Post => Index_Of_Minimum'Result in Values'Range
   is
      Min : Positive;
   begin
      Min := Values'First;
      for Index in Values'Range loop
         pragma Loop_Invariant (Min in Values'Range);
         if Values (Index) < Values (Min) then
            Min := Index;
         end if;
      end loop;
      return Min;
   end Index_Of_Minimum;


   procedure Selection_Sort (Values : in out Nat_Array) is
      Smallest : Positive;  -- Index of the smallest value in the unsorted part
   begin -- Selection_Sort
      if Values'Length = 0 then
         return;
      end if;

      for Current in Values'First .. Values'Last - 1 loop
         Smallest := Index_Of_Minimum (Values (Current .. Values'Last));

         if Smallest /= Current then
            Swap (Values => Values,
                  X      => Current,
                  Y      => Smallest);
         end if;

         pragma Loop_Invariant (Is_Perm (Values'Loop_Entry, Values));
      end loop;

   end Selection_Sort;

end Sort;
