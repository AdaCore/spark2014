package Types_With_Invariants with SPARK_Mode is
   type My_Integer is private;

   type Container (C : Natural) is private;

   function Get (C : Container; I : Positive) return My_Integer with
     Pre => I <= C.C;

   procedure Set (C : in out Container; I : Positive; E : My_Integer) with
     Pre => I <= C.C;

   procedure Test (I : Positive; E : My_Integer) with Ghost;

   type T is private;

   type S is private;

   type A is private with Default_Initial_Condition => False;

   type U (<>) is private;

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

   type T is new Integer with Type_Invariant => T /= 0, Default_Value => 1;

   type R (C : T) is null record; --@INVARIANT_CHECK:FAIL

   subtype Bad_R is R (0);

   type S is new T with Default_Value => 0; --@INVARIANT_CHECK:FAIL

   type A is array (Positive range 1 .. 100) of Integer with --@INVARIANT_CHECK:PASS
     Type_Invariant          => A (A'First) /= 0 and then (for all I in A'Range => A (I) /= 0),
     Default_Component_Value => 0;

   type U is array (Positive range <>) of Integer with --@INVARIANT_CHECK:FAIL
     Type_Invariant          => U (U'First) /= 1 and then (for all I in U'Range => U (I) /= 0), --@INDEX_CHECK:FAIL
     Default_Component_Value => 1;

   subtype A2 is U (1 .. 100);

end Types_With_Invariants;
