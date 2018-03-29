package Types_With_Invariants_Auto is
   type My_Integer is private;

   function To_Integer (X : My_Integer) return Integer;

   function From_Integer (X : Integer) return My_Integer with
     Pre => X > Integer'First;

   type My_Integer_Bad is private;

   function To_Integer (X : My_Integer_Bad) return Integer;

   function From_Integer (X : Integer) return My_Integer_Bad with
     Pre => X > Integer'First;

private
   type My_Integer is record
      Sign : Boolean := True;
      Val  : Natural := 0;
   end record
     with Type_Invariant => (if Val = 0 then Sign);

   function To_Integer (X : My_Integer) return Integer is
      (if X.Sign then X.Val else - X.Val);

   function From_Integer (X : Integer) return My_Integer is
     ((Sign => X >= 0, Val => abs (X)));

   Zero_Is_Positive : Boolean := True;

   type My_Integer_Bad is record
      Sign : Boolean := True;
      Val  : Natural := 0;
   end record
     with Type_Invariant => (if Val = 0 then Sign = Zero_Is_Positive);

   function To_Integer (X : My_Integer_Bad) return Integer is
      (if X.Sign then X.Val else - X.Val);

   function From_Integer (X : Integer) return My_Integer_Bad is
     ((Sign => X >= 0, Val => abs (X)));

end Types_With_Invariants_Auto;
