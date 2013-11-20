procedure P (A, B : Integer) is
   type T is array (A .. B) of Integer;
   Tab : T;
   J, K : Integer;
begin
   --  one simple Loop_Variant

   J := A;
   while J <= B loop
      Tab (J) := J;
      J := J + 1;
      pragma Loop_Variant (Increases => J);
   end loop;

   --  one complex Loop_Variant

   J := A;
   K := 0;
   while J + K <= B loop
      Tab (J + K) := 0;
      if J < 100 then
         J := J + 1;
      else
         K := K + 1;
      end if;
      pragma Loop_Variant (Increases => J,
                           Increases => K);
   end loop;

   --  two colocated Loop_Variant

   J := A;
   K := 0;
   while J <= B loop
      Tab (J) := J;
      J := J + 1;
      K := K + 1;
      pragma Loop_Variant (Increases => J);
      pragma Loop_Variant (Increases => K);
   end loop;

   --  one simple Loop_Variant before Loop_Invariant

   J := A;
   while J <= B loop
      Tab (J) := J;
      J := J + 1;
      pragma Loop_Variant (Increases => J);
      pragma Loop_Invariant (for all L in A .. J - 1 => Tab (L) = L);
   end loop;

   --  one simple Loop_Variant after Loop_Invariant

   J := A;
   while J <= B loop
      Tab (J) := J;
      J := J + 1;
      pragma Loop_Invariant (for all L in A .. J - 1 => Tab (L) = L);
      pragma Loop_Variant (Increases => J);
   end loop;

   --  multiple colocated Loop_Variant and Loop_Invariant

   J := A;
   K := 0;
   while J <= B loop
      Tab (J) := J;
      J := J + 1;
      K := K + 1;
      pragma Loop_Invariant (J = A + K);
      pragma Loop_Variant (Increases => J);
      pragma Loop_Invariant (for all L in A .. J - 1 => Tab (L) = L);
      pragma Loop_Variant (Increases => K);
      pragma Loop_Invariant (for all L in A .. A + K - 1 => Tab (L) = L);
   end loop;

   J := A;
   K := 0;
   while J <= B loop
      Tab (J) := J;
      J := J + 1;
      K := K + 1;
      pragma Loop_Invariant (J = A + K);
      pragma Loop_Invariant (for all L in A .. J - 1 => Tab (L) = L);
      pragma Loop_Variant (Increases => J);
      pragma Loop_Variant (Increases => K);
      pragma Loop_Invariant (for all L in A .. A + K - 1 => Tab (L) = L);
   end loop;

   J := A;
   K := 0;
   while J <= B loop
      Tab (J) := J;
      J := J + 1;
      K := K + 1;
      pragma Loop_Variant (Increases => J);
      pragma Loop_Invariant (J = A + K);
      pragma Loop_Invariant (for all L in A .. J - 1 => Tab (L) = L);
      pragma Loop_Invariant (for all L in A .. A + K - 1 => Tab (L) = L);
      pragma Loop_Variant (Increases => K);
   end loop;

end P;
