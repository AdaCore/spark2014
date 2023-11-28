with SPARK.Big_Integers; use type SPARK.Big_Integers.Big_Integer;

with Int_Lists; use Int_Lists;

procedure Use_Lists with SPARK_Mode, Always_Terminates is
   use Int_Lists.Seqs;

   procedure Set_All_To_Zero (L : access List) with
     Post => Length (Model (L)) = Length (Model (L))'Old --@POSTCONDITION:PASS
     and then (for all E of Model (L) => E = 0);

   procedure Set_All_To_Zero (L : access List) is
      X : access List := L;
   begin
      while X /= null loop
         pragma Loop_Invariant
           (Length (Model (At_End (L))) - Length (Model (X))'Loop_Entry = Length (Model (At_End (X))) - Length (Model (X)));
         pragma Loop_Invariant
           (for all P in Model (At_End (L)) =>
              (if P <= Length (Model (At_End (X))) then Get (Model (At_End (L)), P) = Get (Model (At_End (X)), P)));
         pragma Loop_Invariant
           (for all P in Model (At_End (L)) =>
              (if P > Length (Model (At_End (X))) then Get (Model (At_End (L)), P) = 0));
         pragma Loop_Variant (Decreases => Length (Model (X)));
         Set (X, 0);
         X := Next (X);
      end loop;
      pragma Assert (for all E of Model (At_End (L)) => E = 0);
   end Set_All_To_Zero;
begin
    -- Test case: one entry
   declare
      L : List_Acc := null;
   begin
      Insert (L, 2);
      Insert (L, 1);
      Set_All_To_Zero(L);
      pragma Assert(Get(L) = 0 and then Next(L) /= null and then Get(Next(L)) = 0 and then Next(Next(L)) = null);
      Delete(L);
      Delete(L);
      pragma Unused(L);
   end;
end Use_Lists;
