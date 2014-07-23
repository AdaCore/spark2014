package Static_Discr with SPARK_Mode is
   type Nat_Array is array (Positive range <>) of Natural;

   Max : constant Natural := 100;

   type I_Holder (Unused, C : Natural) is record
      Content : Nat_Array (1 .. C);
   end record;

   type Holder (Unused, C : Natural) is record
      Content : I_Holder (Unused, C);
      Length  : Natural;
   end record;

   subtype Holder_Max is Holder (Max, Max);

   function Search_Max (A : Holder_Max; E : Natural) return Natural with
     Pre  => A.Length <= A.C,
     Post => Search_Max'Result <= A.Length
       and then (if Search_Max'Result = 0 then
                   (for all I in 1 .. A.Length => A.Content.Content (I) /= E)
                     else A.Content.Content (Search_Max'Result) = E);

   function Search (A : Holder; E : Natural) return Natural with
     Pre  => A.C in A.Length .. Max,
     Post => Search'Result <= A.Length
       and then (if Search'Result = 0 then
                   (for all I in 1 .. A.Length => A.Content.Content (I) /= E)
                     else A.Content.Content (Search'Result) = E);

   function Search_Array (A : Nat_Array; E : Natural) return Natural with
     Pre  => A'First = 1 and then A'Last in 0 .. Max,
     Post => Search_Array'Result <= A'Last
       and then (if Search_Array'Result = 0 then
                   (for all I in A'Range => A (I) /= E)
                     else A (Search_Array'Result) = E);
end;
