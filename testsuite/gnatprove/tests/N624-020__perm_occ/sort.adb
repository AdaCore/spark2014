package body Sort
   with SPARK_Mode
is

   -----------------------------------------------------------------------------
   procedure Swap (Values : in out Array_Type;
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
      Init   : constant Array_Type := Values;
      Interm : Array_Type;
      HR     : True_Bool;

      --  Ghost function
      function Prove_Post return True_Bool with
        Pre  => X in Init'Range and then Y in Init'Range and then
        Interm = Set (Init, X, Init (Y)) and then
        Values = Set (Interm, Y, Init (X)),
        Post => Is_Perm (Init, Values) is
         HR : True_Bool;
      begin
         for E in Natural loop
            HR := Occ_Set (Init, X, Init (Y), E);
            HR := Occ_Eq (Interm, Set (Init, X, Init (Y)), E);
            HR := Occ_Set (Interm, Y, Init (X), E);
            HR := Occ_Eq (Values, Set (Interm, Y, Init (X)), E);
            pragma Loop_Invariant (for all F in Natural'First .. E =>
                                     Occ (Init, F) = Occ (Values, F));
         end loop;
         return HR;
      end Prove_Post;

   begin
      Temp       := Values (X);
      Values (X) := Values (Y);

      --  Ghost code
      Interm := Values;

      Values (Y) := Temp;

      --  Ghost code
      HR := Prove_Post;
   end Swap;

   -- Finds the index of the smallest element in the array
   function Index_Of_Minimum (Values : in Array_Type; First, Last : Index)
                              return Positive
     with
       Pre  => First <= Last and then First in Values'Range and then
     Last in Values'Range,
       Post => Index_Of_Minimum'Result in First .. Last
   is
      Min : Positive;
   begin
      Min := First;
      for Index in First .. Last loop
         pragma Loop_Invariant (Min in First .. Last);
         if Values (Index) < Values (Min) then
            Min := Index;
         end if;
      end loop;
      return Min;
   end Index_Of_Minimum;

   procedure Selection_Sort (Values : in out Array_Type) is
      Smallest : Positive;  -- Index of the smallest value in the unsorted part

      --  Ghost variables
      Init     : constant Array_Type := Values;
      Prec     : Array_Type := Values;
      HR       : True_Bool;
   begin -- Selection_Sort

      for Current in Values'First .. Values'Last - 1 loop
         Smallest := Index_Of_Minimum (Values, Current, Values'Last);

         if Smallest /= Current then
            Prec := Values;

            Swap (Values => Values,
                  X      => Current,
                  Y      => Smallest);
         end if;

         pragma Loop_Invariant (Is_Perm (Values'Loop_Entry, Values));
      end loop;

   end Selection_Sort;

end Sort;
