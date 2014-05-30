package body dynamic_types with SPARK_Mode is

   function Search (A : Nat_Array; C : Natural) return Natural is
      subtype A_Range is Positive range A'Range;

      type Wrapper is array (1 .. 1) of A_Range;

      type Result_Type is record
         From   : Wrapper;
         Result : Natural;
      end record;

      function Search_Range (From : Natural) return Result_Type with
        Pre  => From in A'Range,
      --  and then A_Range'First = A'First and then A_Range'Last = A'Last,
      --  needed for the proof of Search_Range but can be stated for now
      --  because of N513-030
        Post => (Search_Range'Result.Result = 0
                 and then (for all I in From .. Search_Range'Result.From (1) =>
                               A (I) /= C))
        or else (Search_Range'Result.Result in A'Range
                 and then A (Search_Range'Result.Result) = C);

      function Search_Range (From : Natural) return Result_Type is
      begin
         if A (From) = C then
            return Result_Type'(From => (1 => From), Result => From);
         else
            return Result_Type'(From => (1 => From), Result => 0);
         end if;
      end Search_Range;

      From   : A_Range := A'First;
      Result : Natural;
      Tmp    : Result_Type;
   begin
      loop
         pragma Loop_Invariant
           (for all I in A'First .. From - 1 => A (I) /= C);
         Tmp := Search_Range (From);
         Result := Tmp.Result;
         From := Tmp.From (1);
         if Result > 0 then
            return Result;
         end if;
         if From = A'Last then
            return 0;
         else
            From := From + 1;
         end if;
      end loop;
   end Search;


end;
