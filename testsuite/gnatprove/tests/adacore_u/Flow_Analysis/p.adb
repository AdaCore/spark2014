package body P with SPARK_Mode is
   Increment : constant Natural := 10;

   procedure Incr_Step_Function (A : in out Array_Of_Positives) is
      Threshold : Positive := Positive'Last;
      procedure Incr_Until_Threshold (I : Integer) with
        Pre    => I in A'Range,
        Global => (Input  => Threshold,
                   In_Out => A);

      procedure Incr_Until_Threshold (I : Integer) is
      begin
         if Threshold - Increment <= A (I) then
            A (I) := Threshold;
         else
            A (I) := A (I) + Increment;
         end if;
      end Incr_Until_Threshold;
   begin
      for I in A'Range loop
         if I > A'First then
            Threshold := A (I - 1);
         end if;
         Incr_Until_Threshold (I);
      end loop;
   end Incr_Step_Function;

   procedure Search_Array (A      :     Array_Of_Positives;
                           E      :     Positive;
                           Result : out Integer;
                           Found  : out Boolean) is
   begin
      for I in A'range loop
         if A (I) = E then
            Result := I;
            Found  := True;
            return;
         end if;
      end loop;
      Found := False;
   end Search_Array;

   Not_Found : exception;

   procedure Search_Array (A      :     Array_Of_Positives;
                           E      :     Positive;
                           Result : out Integer) is
   begin
      for I in A'range loop
         if A (I) = E then
            Result := I;
            return;
         end if;
         pragma Loop_Invariant (for all K in A'First .. I => A (K) /= E);
      end loop;
      raise Not_Found;
   end Search_Array;

   procedure Search_Array (A      :     Array_Of_Positives;
                           E      :     Positive;
                           Result : out Search_Result) is
   begin
      for I in A'Range loop
         if A (I) = E then
            Result := (Found   => True,
                       Content => I);
            return;
         end if;
      end loop;
      Result := (Found => False);
   end Search_Array;

   function Size_Of_Biggest_Increasing_Sequence
     (A : Array_Of_Positives) return Natural is
      Max : Natural := 0;
      End_Of_Seq : Boolean;
      Size_Of_Seq : Natural := 0;
      Beginning : Integer := A'First - 1;

      procedure Test_Index (Current_Index : Integer) with
        Global  => (In_Out => (Beginning, Max, Size_Of_Seq),
                    Output => End_Of_Seq,
                    Input  => A),
        Depends => ((Max, End_Of_Seq)        => (A, Current_Index, Max),
                    (Size_Of_Seq, Beginning) =>
                        +(A, Current_Index, Max, Beginning)),
        Pre     => Current_Index in A'Range
          and then Beginning + 1 in A'First .. Current_Index,
        Post    => Beginning in A'First - 1 .. Current_Index;

      procedure Test_Index (Current_Index : Integer) is
      begin
         if A (Current_Index) >= Max then
            Max := A (Current_Index);
            End_Of_Seq := False;
         else
            Max := 0;
            End_Of_Seq := True;
            Size_Of_Seq := Current_Index - Beginning;
            Beginning := Current_Index;
         end if;
      end Test_Index;

      Biggest_Seq : Natural := 0;
   begin
      for I in A'Range loop
         pragma Loop_Invariant (Beginning + 1 in A'First .. I);
         Test_Index (I);
         if End_Of_Seq then
            Biggest_Seq := Natural'Max (Size_Of_Seq, Biggest_Seq);
         end if;
      end loop;
      return Biggest_Seq;
   end Size_Of_Biggest_Increasing_Sequence;

   procedure Init (A : out Permutation) is
   begin
      for I in A'Range loop
         A (I) := I;
      end loop;
   end Init;

   procedure Swap (A : in out Permutation; X, Y : Positive) is
      Tmp : constant Positive := A (X);
   begin
      A (X) := A (Y);
      A (Y) := Tmp;
   end Swap;

   function Cyclic_Permutation (N : Natural) return Permutation is
      A : Permutation (1 .. N);
   begin
      Init (A);
      for I in A'First .. A'Last - 1 loop
         Swap (A, I, I + 1);
      end loop;
      return A;
   end Cyclic_Permutation;

   procedure Swap (X, Y : in out Positive) is
      Tmp : constant Positive := X;
   begin
      X := Y;
      Y := Tmp;
   end Swap;

   procedure Identity (X, Y : in out Positive) is
   begin
      Swap (X, Y);
      Swap (Y, X);
   end Identity;

end P;
