package body Data_Structure.Formal_Model
  with SPARK_Mode
is

   function Find
     (S : Sequence; V : Values_Type; E : Element_Type) return Big_Natural
   is
      I : Big_Natural := Last (S);
   begin
      while I >= 1 loop
         pragma Loop_Invariant (In_Range (I, 1, Last (S)));
         pragma
           Loop_Invariant
             (for all K in Interval'(I + 1, Last (S)) =>
                not Equivalent_Elements (Get (V, Get (S, K)), E));
         pragma Loop_Variant (Decreases => I);
         if Equivalent_Elements (Get (V, Get (S, I)), E) then
            return I;
         end if;
         I := I - 1;
      end loop;
      return 0;
   end Find;

   function Find (S : Sequence; I : Positive_Count_Type) return Big_Natural is
      K : Big_Natural := Last (S);
   begin
      while K >= 1 loop
         if Get (S, K) = I then
            return K;
         end if;
         pragma Loop_Invariant (In_Range (K, 1, Last (S)));
         pragma
           Loop_Invariant
             (for all J in Interval'(K, Last (S)) => Get (S, J) /= I);
         pragma Loop_Variant (Decreases => K);
         K := K - 1;
      end loop;
      return 0;
   end Find;

end Data_Structure.Formal_Model;
