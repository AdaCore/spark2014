package body Dutch_Flag_Lib with SPARK_Mode is

   package body Permutations is
      function Identity return Permutation is
         Result : Permutation := (others => 1);
      begin
         for I in Index_Type loop
            Result (I) := I;
            pragma Loop_Invariant (for all K in 1 .. I => Result (K) = K);
         end loop;
         return Result;
      end Identity;
   end Permutations;

   procedure Flag (Values : in out Color_Array; Result : out Partition_Result)
   is
      Low  : Natural := Values'First;
      Mid  : Natural := Values'First;
      High : Integer := Values'Last;
   begin
      Order_Permutation := Identity;
      while Mid <= High loop
         pragma Loop_Invariant (Is_Permutation (Order_Permutation));
         pragma Loop_Invariant
           (Same_Values (Values'Loop_Entry, Values, Order_Permutation));
         pragma Loop_Invariant (Low >= Values'First);
         pragma Loop_Invariant (Low <= Mid and then Mid - 1 <= High);
         pragma Loop_Invariant (High <= Values'Last);
         pragma Loop_Variant (Decreases => High - Mid);
         pragma Loop_Invariant
           (for all I in Values'Range =>
              (if I < Low then Values (I) = 0) and then
              (if I > High then Values (I) = 2) and then
              (if (I >= Low and then I < Mid) then Values (I) = 1));

         if Values (Mid) = 0 then
            --  Swap the values at positions Low and Mid, and perform the
            --  matching swap of the original indices in Order_Permutation
            --  (a genuine swap).
            declare
               Temp_Value            : constant Color_Value := Values (Low);
               Temp_Permutation_Index : constant Index_Type :=
                 Order_Permutation (Low) with Ghost;
            begin
               Values (Low)              := Values (Mid);
               Values (Mid)              := Temp_Value;
               Order_Permutation (Low)   := Order_Permutation (Mid);
               Order_Permutation (Mid)   := Temp_Permutation_Index;
            end;
            Low := Low + 1;
            Mid := Mid + 1;

         elsif Values (Mid) = 1 then
            --  We found a 1: it is already in the middle region, so we simply
            --  advance the read cursor.
            Mid := Mid + 1;

         else
            --  We found a 2: send it to the region of 2s at the end, and pull
            --  back the boundary of that region (a genuine Mid/High swap).
            declare
               Temp_Value            : constant Color_Value := Values (High);
               Temp_Permutation_Index : constant Index_Type :=
                 Order_Permutation (High) with Ghost;
            begin
               Values (High)             := Values (Mid);
               Values (Mid)              := Temp_Value;
               Order_Permutation (High)  := Order_Permutation (Mid);
               Order_Permutation (Mid)   := Temp_Permutation_Index;
            end;
            High := High - 1;
         end if;

         pragma Assert
           (Same_Values (Values'Loop_Entry, Values, Order_Permutation));
         pragma Assert (Is_Permutation (Order_Permutation));
      end loop;

      Result.Low  := Low;
      Result.Mid  := Mid;
      Result.High := High;
   end Flag;

end Dutch_Flag_Lib;
