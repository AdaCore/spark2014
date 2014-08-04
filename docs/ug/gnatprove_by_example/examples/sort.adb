with Perm.Lemma_Subprograms; use Perm.Lemma_Subprograms;
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

       Post => Values =
         Set (Set (Values'Old, X, Values'Old (Y)), Y, Values'Old (X))
   is
      Temp : Integer;

      --  Ghost variables
      Init   : constant Nat_Array (Values'Range) := Values;
      Interm : Nat_Array (Values'Range);

   begin
      Temp       := Values (X);
      Values (X) := Values (Y);

      --  Ghost code
      pragma Assert (Values = Set (Init, X, Init (Y)));
      Interm := Values;

      Values (Y) := Temp;

      --  Ghost code
      pragma Assert (Values = Set (Interm, Y, Init (X)));
   end Swap;

   -- Finds the index of the smallest element in the array
   function Index_Of_Minimum (Values : in Nat_Array)
                              return Positive
     with
       Pre  => Values'Length > 0,
       Post => Index_Of_Minimum'Result in Values'Range and then
       (for all I in Values'Range =>
          Values (Index_Of_Minimum'Result) <= Values (I))
   is
      Min : Positive;
   begin
      Min := Values'First;
      for Index in Values'Range loop
         if Values (Index) < Values (Min) then
            Min := Index;
         end if;
         pragma Loop_Invariant
           (Min in Values'Range and then
              (for all I in Values'First .. Index =>
                   Values (Min) <= Values (I)));
      end loop;
      return Min;
   end Index_Of_Minimum;

   procedure Selection_Sort (Values : in out Nat_Array) is
      Smallest : Positive;  -- Index of the smallest value in the unsorted part

      --  Ghost variable
      Previous : Nat_Array (Values'Range);

      --  Ghost procedure
      procedure Prove_Swap_Perm (Values, Next : Nat_Array; X, Y : Index) with
        Pre  => X in Values'Range and then Y in Values'Range and then
           Next = Set (Set (Values, X, Values (Y)), Y, Values (X)),
        Post => Is_Perm (Values, Next) is
      begin
         for E in Natural loop
            Occ_Set (Values, X, Values (Y), E);
            Occ_Set (Set (Values, X, Values (Y)), Y, Values (X), E);
            Occ_Eq (Next, Set (Set (Values, X, Values (Y)), Y, Values (X)), E);
            pragma Loop_Invariant
              (for all F in Natural'First .. E =>
                 Occ (Values, F) = Occ (Next, F));
         end loop;
      end Prove_Swap_Perm;
   begin
      if Values'Length = 0 then
         return;
      end if;

      for Current in Values'First .. Values'Last - 1 loop
         Smallest := Index_Of_Minimum (Values (Current .. Values'Last));

         if Smallest /= Current then

            --  Ghost code
            Previous := Values;

            Swap (Values => Values,
                  X      => Current,
                  Y      => Smallest);

            --  Ghost code
            Prove_Swap_Perm (Previous, Values, Current, Smallest);
         end if;

         pragma Loop_Invariant
           (for all I in Values'First .. Current =>
              (for all J in I + 1 .. Values'Last =>
                   Values (I) <= Values (J)));
         pragma Loop_Invariant (Is_Perm (Values'Loop_Entry, Values));
      end loop;

   end Selection_Sort;

end Sort;
