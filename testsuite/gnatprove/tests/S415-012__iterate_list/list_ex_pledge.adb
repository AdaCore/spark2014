package body List_Ex_Pledge with SPARK_Mode is

   procedure All_Zero (L : List) is
      Lgth : Natural := Length (L) with Ghost;
      T    : access List_Cell := L;
      I    : Natural := 0 with Ghost;
   begin
      while T /= null loop
         pragma Loop_Invariant (Lgth - I = Length (T));
         pragma Loop_Invariant
           (if Length (At_End_Borrow (T)) <= Natural'Last - I
            then Length (At_End_Borrow (L)) = I + Length (At_End_Borrow (T))
            else Length (At_End_Borrow (L)) = Natural'Last);
         pragma Loop_Invariant
           (for all K in 1 .. I => Get_Nth_Val (At_End_Borrow (L), K) = 0);
         pragma Loop_Invariant
           (for all K in I + 1 .. Length (At_End_Borrow (L)) =>
              Get_Nth_Val (At_End_Borrow (L), K) = Get_Nth_Val (At_End_Borrow (T), K - I));
         pragma Loop_Invariant
           (for all K in 1 .. Length (At_End_Borrow (L)) - I =>
              Get_Nth_Val (At_End_Borrow (L), K + I) = Get_Nth_Val (At_End_Borrow (T), K));

         T.Value := 0;
         T := T.Next;

         I := I + 1;
      end loop;
   end All_Zero;
end List_Ex_Pledge;
