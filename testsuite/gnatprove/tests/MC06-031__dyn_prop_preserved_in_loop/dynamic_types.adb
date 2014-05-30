package body dynamic_types with SPARK_Mode is

   function Search (A : Nat_Array; C : Natural) return Natural is
      subtype A_Range is Positive range A'Range;

      procedure Search_Range (From : in out A_Range; Result : out Natural) with
        Pre  => A_Range'First = A'First and then A_Range'Last = A'Last,
        Post => (Result = 0
                 and then (for all I in From'Old .. From => A (I) /= C))
        or else (Result in A'Range and then A (Result) = C);

      procedure Search_Range (From : in out A_Range; Result : out Natural) is
      begin
         if A (From) = C then
            Result := From;
         else
            Result := 0;
         end if;
      end Search_Range;

      From   : A_Range := A'First;
      Result : Natural;
   begin
      loop
         pragma Loop_Invariant
           (for all I in A'First .. From - 1 => A (I) /= C);
         Search_Range (From, Result);
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
