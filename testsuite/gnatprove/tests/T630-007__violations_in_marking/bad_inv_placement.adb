procedure Bad_Inv_Placement with SPARK_Mode is
   V : Integer;
begin
   for I in 1 .. 10 loop
      declare
         package Nested is
            B : Boolean := I >= 5;
         end Nested;
         function F (X : Natural) return Integer is (X - I);
      begin
         V := F (I);
      end;
      pragma Loop_Invariant (V = 0);
   end loop;
end Bad_Inv_Placement;
