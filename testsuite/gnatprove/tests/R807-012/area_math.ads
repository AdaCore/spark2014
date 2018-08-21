package Area_Math
  with SPARK_Mode => On
is

   Word_Size    : constant := 32;
   Memory_Size  : constant := 2 ** Word_Size;
   type Address_Type is mod Memory_Size;

   type Area_Array is array (Integer range <>) of Address_Type;

   Empty_Array : constant Area_Array (1 .. 0) := (1 .. 0 => 0);

   type Ensemble (Max : Natural) is record
      Size : Natural;
      From : Area_Array (1 .. Max);
      To : Area_Array (1 .. Max);
   end record
     with Predicate => Ensemble.Size <= Ensemble.From'Last and Ensemble.Size <= Ensemble.To'Last;

   function Is_Consistent (E : Ensemble) return Boolean is
      -- REQ_1 all area are ordered, disjoint and distant by at least 1 element outide of the set
     ((for all R in 1 .. E.Size - 1 => E.To (R) < E.From (R + 1) and then E.From (R + 1) - E.To (R) > 1) and
        -- REQ_2 From and To are ordered, there is no empty range
        (for all R in 1 .. E.Size => E.From (R) <= E.To (R)));

   Empty : Ensemble := (Max => 0, Size => 0, From => Empty_Array, To => Empty_Array);

   function E (From, To : Address_Type) return Ensemble;

   procedure Put_Line (E : Ensemble);

   function "<" (B : Address_Type; A : Ensemble) return Boolean
   is (for some R in 1 .. A.Size => B in A.From (R) .. A.To (R))
     with Ghost;

   function "or" (A1, A2 : Ensemble) return Ensemble
     with Post => (for all B in Address_Type => (B < "or"'Result) = (B < A1 or B < A2))
     and "or"'Result.Size <= A1.Size + A2.Size;

   function "and" (A1, A2 : Ensemble) return Ensemble
     with Post => (for all B in Address_Type => (B < "and"'Result) = (B < A1 and B < A2))
     and "and"'Result.Size <= A1.Size + A2.Size;

   -- TODO: have a precondition Is_Consistent (list of disjoint areas)
   -- then start to prove this
   function "not" (E : Ensemble) return Ensemble
     with Pre =>
       Positive'Last - E.Max > 0
         and Is_Consistent (E),
     Post =>
       Is_Consistent ("not"'Result) and then
       (for all B in Address_Type => (B < "not"'Result) = (not B < E)) and then
       "not"'Result.Size <= E.Size + 1 and then
       "not"'Result.Max <= E.Size + 1;

end Area_Math;
