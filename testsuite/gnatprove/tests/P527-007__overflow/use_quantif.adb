package body Use_Quantif with SPARK_Mode is
   procedure P (Fst, Lst : Index_Type) is
      G : Integer := 0;
   begin
      for I in Fst .. Lst loop
         pragma Loop_Invariant
           (for all J in Index_Type'First .. Fst - 2 => Nested.Id (J) = J);
         G := G + 1;
      end loop;
   end P;
end Use_Quantif;
