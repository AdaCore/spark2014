with Declare_Iterable; use Declare_Iterable;

procedure For_Loop_Array with SPARK_Mode is
   A : Nat_Array := (others => 0);
begin
   for E of To_Nat_Array (From_Nat_Array (A)) loop
      pragma Assert (E = 0);
   end loop;
end For_Loop_Array;
