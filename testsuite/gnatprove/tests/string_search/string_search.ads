package String_Search
  with SPARK_Mode
is
   subtype Text is String with Predicate => Text'First = 1;

   --  There is a partial match of the needle at location loc in the
   --  haystack, of length len.
   function Partial_Match_At
     (Needle, Haystack : Text; Loc : Positive; Len : Natural) return Boolean
   is
     (for all I in 1 .. Len => Needle(I) = Haystack(Loc + (I - 1)))
   with Ghost,
        Pre => Len <= Needle'Length
          and then Loc - 1 <= Haystack'Length - Len;

   --  There is a complete match of the needle at location loc in the
   --  haystack.
   function Match_At (Needle, Haystack : Text; Loc : Positive) return Boolean is
     (Loc - 1 <= Haystack'Length - Needle'Length
      and then Partial_Match_At (Needle, Haystack, Loc, Needle'Length))
   with Ghost;

   function Brute_Force (Needle, Haystack : in Text) return Natural with
     Pre  => Needle'Length in 1 .. Haystack'Length,
     Post => Brute_Force'Result in 0 .. Haystack'Length - Needle'Length + 1
       and then
       (if Brute_Force'Result > 0 then
          Match_At (Needle, Haystack, Brute_Force'Result)
        else
          (for all K in Haystack'Range =>
             not Match_At (Needle, Haystack, K)));

   function Brute_Force_Slice (Needle, Haystack : in Text) return Natural with
     Pre  => Needle'Length in 1 .. Haystack'Length,
     Post => Brute_Force_Slice'Result in 0 .. Haystack'Length - Needle'Length + 1
       and then
       (if Brute_Force_Slice'Result > 0 then
          Match_At (Needle, Haystack, Brute_Force_Slice'Result)
        else
          (for all K in Haystack'Range =>
             not Match_At (Needle, Haystack, K)));

   type Shift_Table is array (Character) of Positive;

   procedure Make_Bad_Shift (Needle : Text; Bad_Shift : out Shift_Table) with
     Pre  => Needle'Length < Integer'Last,
     Post => (for all C in Character => Bad_Shift(C) in 1 .. Needle'Length + 1)
       and then (for all C in Character =>
                   (if Bad_Shift(C) = Needle'Length + 1 then
                      (for all K in Needle'Range => C /= Needle(K))
                    else
                      Needle(Needle'Length - Bad_Shift(C) + 1) = C
                      and (for all K in Needle'Length - Bad_Shift(C) + 2 .. Needle'Last => Needle(K) /= C)
                 ));

   function QS (Needle, Haystack : in Text) return Natural with
     Pre => Needle'Length < Integer'Last
       and then Haystack'Length < Integer'Last - 1
       and then Needle'Length in 1 .. Haystack'Length,
     Post => QS'Result in 0 .. Haystack'Length - Needle'Length + 1
       and then
       (if QS'Result > 0 then
          Match_At (Needle, Haystack, QS'Result)
        else
          (for all K in Haystack'Range =>
             not Match_At (Needle, Haystack, K)));

end String_Search;
