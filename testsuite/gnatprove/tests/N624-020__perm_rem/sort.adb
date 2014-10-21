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
      Init   : constant Array_Type := Values with Ghost;
      Interm : Array_Type with Ghost;
      HR     : True_Bool with Ghost;
   begin
      Temp       := Values (X);
      Values (X) := Values (Y);

      --  Ghost code
      Interm := Values;
      pragma Assert (Remove (Init, X) = Remove (Interm, X));

      Values (Y) := Temp;
      pragma Assert (Remove (Interm, Y) = Remove (Values, Y));

      --  Ghost code
      if X > Y then
         declare
            HR : True_Bool with Ghost;
         begin
            HR := Remove_Eq (Remove (Interm, Y), Remove (Values, Y), X - 1);
            HR := Remove_Swap (Interm, Y, X);
            pragma Assert (Remove (Remove (Interm, X), Y) =
                             Remove (Remove (Interm, Y), X - 1));
            pragma Assert (Remove (Remove (Interm, X), Y) =
                             Remove (Remove (Values, Y), X - 1));
            HR := Remove_Swap (Values, Y, X);
            pragma Assert (Remove (Remove (Interm, X), Y) =
                             Remove (Remove (Values, X), Y));
            HR := Remove_Eq (Remove (Init, X), Remove (Interm, X), Y);
            pragma Assert_And_Cut (Remove (Remove (Init, X), Y) =
                                     Remove (Remove (Values, X), Y));
         end;
         HR := Perm_Reflexive (Remove (Remove (Init, X), Y),
                               Remove (Remove (Values, X), Y));
         HR := Remove_Swap (Values, Y, X);
         HR := Perm_Reflexive (Remove (Remove (Values, X), Y),
                               Remove (Remove (Values, Y), X - 1));
         HR := Perm_Transitive (Remove (Remove (Init, X), Y),
                                Remove (Remove (Values, X), Y),
                                Remove (Remove (Values, Y), X - 1));
         pragma Assert (Remove (Init, X) (Y) = Remove (Values, Y) (X - 1));
         pragma Assert (Is_Perm (Remove (Init, X), Remove (Values, Y)));
      else
         declare
            HR : True_Bool with Ghost;
         begin
            HR := Remove_Eq (Remove (Interm, Y), Remove (Values, Y), X);
            HR := Remove_Swap (Interm, X, Y);
            pragma Assert (Remove (Remove (Interm, X), Y - 1) =
                             Remove (Remove (Interm, Y), X));
            pragma Assert (Remove (Remove (Interm, X), Y - 1) =
                             Remove (Remove (Values, Y), X));
            HR := Remove_Swap (Values, X, Y);
            pragma Assert (Remove (Remove (Interm, X), Y - 1) =
                             Remove (Remove (Values, X), Y - 1));
            HR := Remove_Eq (Remove (Init, X), Remove (Interm, X), Y - 1);
            pragma Assert_And_Cut (Remove (Remove (Init, X), Y - 1) =
                                     Remove (Remove (Values, X), Y - 1));
         end;
         HR := Perm_Reflexive (Remove (Remove (Init, X), Y - 1),
                               Remove (Remove (Values, X), Y - 1));
         HR := Remove_Swap (Values, X, Y);
         HR := Perm_Reflexive (Remove (Remove (Values, X), Y - 1),
                               Remove (Remove (Values, Y), X));
         HR := Perm_Transitive (Remove (Remove (Init, X), Y - 1),
                                Remove (Remove (Values, X), Y - 1),
                                Remove (Remove (Values, Y), X));
         pragma Assert (Remove (Init, X) (Y - 1) = Remove (Values, Y) (X));
         pragma Assert (Is_Perm (Remove (Init, X), Remove (Values, Y)));
      end if;
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
      Init     : constant Array_Type := Values with Ghost;
      Prec     : Array_Type := Values with Ghost;
      HR       : True_Bool with Ghost;
   begin -- Selection_Sort

      HR := Perm_Reflexive (Values, Values);
      for Current in Values'First .. Values'Last - 1 loop
         Smallest := Index_Of_Minimum (Values, Current, Values'Last);

         if Smallest /= Current then
            Prec := Values;

            Swap (Values => Values,
                  X      => Current,
                  Y      => Smallest);

            HR := Perm_Transitive (Init, Prec, Values);
         end if;

         pragma Loop_Invariant (Is_Perm (Values'Loop_Entry, Values));
      end loop;

   end Selection_Sort;

end Sort;
