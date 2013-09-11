package body Slice_Sums is

   function Maximal_Sum_Slice_Bounds (X : Vector) return Slice_Bounds is
      -- extreme brute force solution (cubic, not even quadratic time).

      Max_Sum : Natural := 0;
      Result : Slice_Bounds;
      Current_Slice : Slice_Bounds;
      Current_Sum : Integer;
   begin
      Result := Slice_Bounds'(Lo => 1, Hi => 0);

      for Lo in Index range X'First .. X'Last loop
         pragma Loop_Invariant
           (for all Lo_Index in Index range X'First .. Lo - 1 =>
              (for all Hi_Index in Index range X'First .. X'Last =>
                   (Max_Sum >= Sum (X, Slice_Bounds'(Lo_Index, Hi_Index)))));
         pragma Loop_Invariant
           (if Result.Lo <= Result.Hi then
              (X'First <= Result.Lo and then
               Result.Hi <= X'Last and then
               Max_Sum = Sum (X, Result)));

         for Hi in Index range X'First .. X'Last loop
            pragma Loop_Invariant
              ((for all Lo_Index in Index range X'First .. Lo - 1 =>
                    (for all Hi_Index in Index range X'First .. X'Last =>
                       (Max_Sum >= Sum (X, Slice_Bounds'(Lo_Index,
                        Hi_Index))))) and
                 (for all Hi_Index in Index range X'First .. Hi - 1 =>
                      (Max_Sum >= Sum (X, Slice_Bounds'(Lo, Hi_Index)))));
            pragma Loop_Invariant
              (if Result.Lo <= Result.Hi then
                 (X'First <= Result.Lo and then
                  Result.Hi <= X'Last and then
                  Max_Sum = Sum (X, Result)));

            Current_Slice := Slice_Bounds'(Lo, Hi);
            Current_Sum := Sum (X, Current_Slice);
            if Current_Sum > Max_Sum then
               Result := Current_Slice;
               Max_Sum := Current_Sum;
            end if;
         end loop;
      end loop;

      return Result;
   end Maximal_Sum_Slice_Bounds;

   function Maximal_Sum_Slice_Bounds_2
     (X : Vector) return Slice_Bounds is
      -- linear time version

      Max_Sum : Natural := 0;
      Current_Sum : Integer := 0;

      Current_Lo  : Index;
      Result : Slice_Bounds;
   begin
      if X'First > X'Last then
         Result := Slice_Bounds'(Lo => 1, Hi => 0);
      else
         Result := Slice_Bounds'(Lo => X'First, Hi => 0);
         Current_Lo := Result.Lo;

         for Current_Hi in Index range X'First .. X'Last loop
            pragma Loop_Invariant
              (X'First <= Current_Lo and then
               Current_Lo <= Current_Hi and then
               0 <= Current_Sum and then
               Current_Sum <= (Current_Hi - Current_Lo) * Vector_Element'Last);
            pragma Loop_Invariant
              (Current_Sum = Sum (X, Slice_Bounds'(Current_Lo,
                        Current_Hi - 1)));
            pragma Loop_Invariant
              (if Result.Lo <= Result.Hi then
                 (X'First <= Result.Lo and then
                  Result.Hi <= X'Last and then
                  Max_Sum = Sum (X, Result)));
            pragma Loop_Invariant
              (for all Lo_Index in Index range X'First .. Current_Hi - 1 =>
                    (for all Hi_Index in Index range X'First .. Current_Hi -1 =>
                       (Max_Sum >= Sum (X, Slice_Bounds'(Lo_Index,
                        Hi_Index)))));
            pragma Loop_Invariant
              (for all Lo_Index in Index range X'First .. Current_Lo - 1 =>
                 Sum (X, Slice_Bounds'(Lo_Index, Current_Lo - 1)) <= 0);
            pragma Loop_Invariant
              (for all Hi_Index in Index range Current_Lo .. Current_Hi - 1 =>
                 Sum (X, Slice_Bounds'(Current_Lo, Hi_Index)) >= 0);

            Current_Sum := Current_Sum + X (Current_Hi);
            if Current_Sum > Max_Sum then
               Max_Sum := Current_Sum;
               Result.Lo := Current_Lo;
               Result.Hi := Current_Hi;
            elsif Current_Sum < 0 then
               if Current_Hi /= Index'Last then
                  Current_Lo := Current_Hi + 1;
                  Current_Sum := 0;
               end if;
            end if;
         end loop;
      end if;

      return Result;
   end Maximal_Sum_Slice_Bounds_2;

end Slice_Sums;
