package Types_With_Invariants with SPARK_Mode is
   type My_Integer is private;

   type Container (C : Natural) is private;

   function Get (C : Container; I : Positive) return My_Integer with
     Pre => I <= C.C;

   procedure Set (C : in out Container; I : Positive; E : My_Integer) with
     Pre => I <= C.C;

   procedure Test (I : Positive; E : My_Integer) with Ghost;

private
   type My_Integer is record
      Sign : Boolean := True;
      Val  : Natural := 0;
   end record
     with Type_Invariant => (if Val = 0 then Sign);

   function To_Integer (X : My_Integer) return Integer is
      (if X.Sign then X.Val else - X.Val);

   function From_Integer (X : Integer) return My_Integer is
     ((Sign => X >= 0, Val => abs (X)))
   with
     Pre => X > Integer'First;

   type My_Array is array (Positive range <>) of My_Integer;

   type Container (C : Natural) is record
      Content : My_Array (1 .. C);
   end record;

   function Get (C : Container; I : Positive) return My_Integer is
      (C.Content (I));

end Types_With_Invariants;
