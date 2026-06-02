with SPARK.Big_Integers; use SPARK.Big_Integers;

procedure Test with SPARK_Mode
is
   type List_Cell;

   type List is access List_Cell;

   type List_Cell is record
      V : Integer;
      N : List;
   end record;

   function Length (X : access constant List_Cell) return Big_Natural is
     (if X = null then 0 else 1 + Length (X.N))
       with Subprogram_Variant => (Structural => X);

   function At_End (X : access constant List_Cell) return access constant List_Cell is (X) with
     Ghost, Annotate => (GNATprove, At_End_Borrow);

   procedure P (L : in out List) is
      X : access List_Cell := L;

      package Nested is
         procedure Next (V : out Integer) with
           Pre => X /= null,
           Post => Length (At_End (X'Old)) = Length (At_End (X)) + 1;

         procedure Next_2 (V : out Integer) with
           Pre => X /= null;
      end Nested;

      package body Nested is
         procedure Next (V : out Integer) is
         begin
            V := X.V;
            X := X.N;
         end Next;

         procedure Next_2 (V : out Integer) with
           Refined_Post => Length (At_End (X'Old)) = Length (At_End (X)) + 1
         is
         begin
            V := X.V;
            X := X.N;
         end Next_2;
      end Nested;
   begin
      null;
   end P;
begin
   null;
end;
