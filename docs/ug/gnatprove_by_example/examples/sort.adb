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

       Post => Is_Perm (Values'Old, Values)
     and Values (X) = Values'Old (Y)
     and Values (Y) = Values'Old (X)
     and (for all Z in Values'Range =>
            (if Z /= X and Z /= Y then Values (Z) = Values'Old (Z)))
   is
      Temp : Integer;

      --  Ghost variables
      Init   : constant Nat_Array (Values'Range) := Values with Ghost;
      Interm : Nat_Array (Values'Range) with Ghost;

      --  Ghost procedure
      procedure Prove_Perm with Ghost,
        Pre  => X in Values'Range and then Y in Values'Range and then
        Is_Set (Init, X, Init (Y), Interm)
        and then Is_Set (Interm, Y, Init (X), Values),
        Post => Is_Perm (Init, Values)
      is
      begin
         for E in Natural loop
            Occ_Set (Init, X, Init (Y), E, Interm);
            Occ_Set (Interm, Y, Init (X), E, Values);
            pragma Loop_Invariant
              (for all F in Natural'First .. E =>
                 Occ (Values, F) = Occ (Init, F));
         end loop;
      end Prove_Perm;

   begin
      Temp       := Values (X);
      Values (X) := Values (Y);

      --  Ghost code
      pragma Assert (Is_Set (Init, X, Init (Y), Values));
      Interm := Values;

      Values (Y) := Temp;

      --  Ghost code
      pragma Assert (Is_Set (Interm, Y, Init (X), Values));
      Prove_Perm;
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

         pragma Loop_Invariant
           (for all I in Values'First .. Current =>
              (for all J in I + 1 .. Values'Last =>
                   Values (I) <= Values (J)));
         pragma Loop_Invariant (Is_Perm (Values'Loop_Entry, Values));
      end loop;

   end Selection_Sort;

end Sort;
