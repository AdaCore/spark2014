procedure Dyn_Pred_In_Loop with SPARK_Mode is
  type Nat_Array is array (1 .. 10) of Natural;
  A : Nat_Array;
begin
  for I in A'Range loop
     declare
        subtype T is Natural with
           Dynamic_Predicate => T * I < Integer'Last;
        X : Natural := 1;
     begin
        while X in T loop
           X := X * I;
        end loop;
        A (I) := X;
     end;
  end loop;
end Dyn_Pred_In_Loop;
