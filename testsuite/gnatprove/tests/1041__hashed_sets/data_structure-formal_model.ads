with SPARK.Big_Integers;  use SPARK.Big_Integers;
with SPARK.Big_Intervals; use SPARK.Big_Intervals;
with SPARK.Containers.Functional.Maps;
with SPARK.Containers.Functional.Infinite_Sequences;

package Data_Structure.Formal_Model
  with SPARK_Mode, Ghost, Always_Terminates
is
   package Memory_Index_To_Big is new Signed_Conversions (Count_Type);
   function To_Big (X : Count_Type) return Big_Integer
   renames Memory_Index_To_Big.To_Big_Integer;

   package Memory_Index_Sequences is new
     SPARK.Containers.Functional.Infinite_Sequences (Positive_Count_Type);

   package Index_To_Value_Maps is new
     SPARK.Containers.Functional.Maps (Positive_Count_Type, Element_Type);

   use Memory_Index_Sequences;
   use Index_To_Value_Maps;

   subtype Values_Type is Index_To_Value_Maps.Map;

   function Is_Add
     (S1 : Sequence; I : Positive_Count_Type; S2 : Sequence) return Boolean
   is (Length (S2) - 1 = Length (S1)
       and then Get (S2, Last (S2)) = I
       and then S1 <= S2);

   function Is_Add
     (S1 : Sequence; P : Big_Positive; I : Positive_Count_Type; S2 : Sequence)
      return Boolean
   is (Length (S2) - 1 = Length (S1)
       and then P <= Last (S2)
       and then Get (S2, P) = I
       and then Range_Equal (S1, S2, 1, P - 1)
       and then Range_Shifted (S1, S2, P, Last (S1), 1));

   function Is_Remove
     (S1 : Sequence; P : Big_Positive; S2 : Sequence) return Boolean
   is (Length (S2) = Length (S1) - 1
       and then P <= Last (S1)
       and then Range_Equal (S1, S2, 1, P - 1)
       and then Range_Shifted (S2, S1, P, Last (S2), 1));

   function Is_Move
     (S1 : Sequence; P1, P2 : Big_Positive; S2 : Sequence) return Boolean
   is (Length (S1) = Length (S2)
       and then In_Range (P1, 1, Last (S1))
       and then In_Range (P2, 1, Last (S2))
       and then Get (S1, P1) = Get (S2, P2)
       and then (for all P in Interval'(1, Last (S1)) =>
                   (if (P < P1 and P < P2) or (P > P1 and P > P2)
                    then Get (S2, P) = Get (S1, P)))
       and then (for all P in Interval'(1, Last (S2)) =>
                   (if P >= P1 and P < P2 then Get (S2, P) = Get (S1, P + 1)))
       and then (for all P in Interval'(1, Last (S2)) =>
                   (if P > P2 and P <= P1 then Get (S1, P - 1) = Get (S2, P)))
       and then (for all P in Interval'(1, Last (S1)) =>
                   (if P > P1 and P <= P2 then Get (S2, P - 1) = Get (S1, P)))
       and then (for all P in Interval'(1, Last (S1)) =>
                   (if P >= P1 and P < P2 then Get (S1, P + 1) = Get (S2, P))));

   function Find (S : Sequence; I : Positive_Count_Type) return Big_Natural
   with
     Post =>
       Find'Result <= Last (S)
       and then (if Find'Result > 0 then Get (S, Find'Result) = I)
       and then (for all K in Interval'(Find'Result + 1, Last (S)) =>
                   Get (S, K) /= I);

   function Find
     (S : Sequence; V : Values_Type; E : Element_Type) return Big_Natural
   with
     Pre  => (for all I of S => Has_Key (V, I)),
     Post =>
       Find'Result <= Last (S)
       and then (if Find'Result > 0
                 then Equivalent_Elements (Get (V, Get (S, Find'Result)), E))
       and then (for all K in Interval'(Find'Result + 1, Last (S)) =>
                   not Equivalent_Elements (Get (V, Get (S, K)), E));

   function No_Duplicated_Indexes (B : Sequence) return Boolean
   is (for all P1 in Interval'(1, Last (B)) =>
         (for all P2 in Interval'(1, Last (B)) =>
            (if P1 /= P2 then Get (B, P2) /= Get (B, P1))));

end Data_Structure.Formal_Model;
