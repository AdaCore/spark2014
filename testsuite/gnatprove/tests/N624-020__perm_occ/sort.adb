package body Sort
   with SPARK_Mode
is

   -----------------------------------------------------------------------------
   procedure Swap (Values : in out Nat_Array;
                   X      : in     Positive;
                   Y      : in     Positive)
   with
      Pre  => (X in Values'Range and then
                  Y in Values'Range and then
                  X /= Y),

      Post => Is_Perm (Values'Old, Values)
   is
      Temp : Integer;

      --  Ghost variables
      Init   : constant Nat_Array (Values'Range) := Values;
      Interm : Nat_Array (Values'Range);

      --  Ghost procedure
      procedure Prove_Post with
        Pre  => X in Init'Range and then Y in Init'Range and then
        Interm = Set (Init, X, Init (Y)) and then
        Values = Set (Interm, Y, Init (X)),
        Post => Is_Perm (Init, Values) is
      begin
         for E in Natural loop
            Occ_Set (Init, X, Init (Y), E);
            Occ_Eq (Interm, Set (Init, X, Init (Y)), E);
            Occ_Set (Interm, Y, Init (X), E);
            Occ_Eq (Values, Set (Interm, Y, Init (X)), E);
            pragma Loop_Invariant (for all F in Natural'First .. E =>
                                     Occ (Init, F) = Occ (Values, F));
         end loop;
      end Prove_Post;

   begin
      Temp       := Values (X);
      Values (X) := Values (Y);

      --  Ghost code
      Interm := Values;

      Values (Y) := Temp;

      --  Ghost code
      Prove_Post;
   end Swap;

   -- Finds the index of the smallest element in the array
   function Index_Of_Minimum (Values : in Nat_Array)
                              return Positive
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
   begin
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
