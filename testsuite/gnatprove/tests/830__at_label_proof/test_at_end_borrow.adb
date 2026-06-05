pragma Extensions_Allowed (All_Extensions);

with SPARK.Big_Integers; use SPARK.Big_Integers;

procedure Test_At_End_Borrow with SPARK_Mode
is
   pragma Unevaluated_Use_Of_Old (Allow);

   type List_Cell;

   type List is access List_Cell;

   type List_Cell is record
      V : Integer;
      N : List;
   end record with Size => 128;

   function Length (X : access constant List_Cell) return Big_Natural is
     (if X = null then 0 else 1 + Length (X.N))
       with Subprogram_Variant => (Structural => X);

   function At_End (X : access constant List_Cell) return access constant List_Cell is (X) with
     Ghost,
     Annotate => (GNATprove, At_End_Borrow);

   procedure P (L : in out List) is
      X : access List_Cell := L;
   begin
      <<Before_Loop>>
      while X /= null loop
         pragma Loop_Invariant
           (if Length (At_End (X)) = Length (X)
            then Length (At_End (X'At (Before_Loop))) = Length (X)'At (Before_Loop));
         <<Loop_Begin>>
         X.V := 0;
         X := X.N;
         declare
            C : constant access constant List_Cell :=
              At_End (X'At (Loop_Begin)) with Ghost;
         begin
            pragma Assert (C.V = 0);
         end;
         pragma Assert (Length (At_End (X'At (Loop_Begin))) = Length (At_End (X)) + 1);
      end loop;
   end P;
begin
   null;
end;
