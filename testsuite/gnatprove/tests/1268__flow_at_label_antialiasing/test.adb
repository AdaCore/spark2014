pragma Extensions_Allowed (All_Extensions);

procedure Test (B1, B2 : in out Integer) with SPARK_Mode is
   subtype Index is Integer range 1 .. 3;

   type Arr is array (Index) of Integer;

   type Rec is record
      A : Index;
      B : Index;
   end record;

   function Increment_And_Return (X : in out Integer) return Integer with
     Side_Effects,
     Global => null,
     Pre => True;

   function Increment_And_Return (X : in out Integer) return Integer is
   begin
      X := X + 1;
      return X;
   end Increment_And_Return;

   A : Arr;
   R : Rec := (A => 1, B => 2);
begin
   <<Init>>
   R.A := Index (B2);

   A (Index (B1'At (Init))) := Increment_And_Return (B1);
   A (R'At (Init).A) := Increment_And_Return (R.A);
end Test;
