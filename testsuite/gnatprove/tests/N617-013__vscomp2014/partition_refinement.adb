package body Partition_Refinement with
  SPARK_Mode
is
   procedure Make_New_Partitions
     (P : in out Partition;
      F : in out Inverse_Partition)
   is
      P_Elem, P_Prime : Interval;
      P_Prime_Index : Partition_Index;
   begin
      for J in 0 .. Partition_Index'Base (Length (P)) - 1 loop
         P_Elem := Element (P, J);
         if P_Elem.Count in 1 .. P_Elem.Last - P_Elem.First then
            P_Prime := Interval'(First => P_Elem.First + P_Elem.Count,
                                 Last  => P_Elem.Last,
                                 Count => 0);
            P_Prime_Index := Partition_Index (Length (P));

            for I in P_Prime.First .. P_Prime.Last loop
               F(I) := P_Prime_Index;
               pragma Loop_Invariant (for all J in Index range P_Prime.First .. I => F(J) = P_Prime_Index);
               pragma Loop_Invariant (for all J in Index range 0 .. P_Prime.First - 1 => F(J) = F'Loop_Entry(J));
               pragma Loop_Invariant (for all J in Index range I + 1 .. Index'Last => F(J) = F'Loop_Entry(J));
            end loop;
         end if;
      end loop;
   end Make_New_Partitions;

end Partition_Refinement;
