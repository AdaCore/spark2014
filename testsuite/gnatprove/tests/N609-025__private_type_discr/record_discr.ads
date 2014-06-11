with Private_Record; use Private_Record;

package Record_Discr with SPARK_Mode is

   type Nat_Array is array (Positive range <>) of Natural;

   type Interm_Result (UpTo : Natural) is record
      To_Search : Nat_Array (1 .. UpTo);
   end record;

   subtype Result_3 is Interm_Result (3);

   function Search_Upto_3 (R : Result_3; E : Natural) return Result_Ty with
     Post => (if Search_Upto_3'Result.Found then
                (Get_Content (Search_Upto_3'Result) <= R.UpTo
                     and then R.To_Search (Get_Content (Search_Upto_3'Result)) = E)
                else (for all I in 1 .. R.Upto => R.To_Search (I) /= E));


   function Search (A : Nat_Array; E : Natural) return Result_Ty with
     Pre  => A'First = 1 and then A'Last >= 0,
     Post => (if Search'Result.Found then A (Get_Content (Search'Result)) = E
                else (for all I in A'Range => A (I) /= E));

   function Search_Upto (R : Interm_Result; E : Natural) return Result_Ty with
     Post => (if Search_Upto'Result.Found then
                (Get_Content (Search_Upto'Result) <= R.UpTo
                     and then R.To_Search (Get_Content (Search_Upto'Result)) = E)
                else (for all I in 1 .. R.Upto => R.To_Search (I) /= E));

end;
