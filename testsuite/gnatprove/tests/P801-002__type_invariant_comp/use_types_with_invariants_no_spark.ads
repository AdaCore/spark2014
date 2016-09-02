with Types_With_Invariants_No_SPARK; use Types_With_Invariants_No_SPARK;

package Use_Types_With_Invariants_No_SPARK with SPARK_Mode is

   type Container (C : Natural) is private;

   function Get (C : Container; I : Positive) return My_Integer with
     Pre => I <= C.C;

   procedure Set (C : in out Container; I : Positive; E : My_Integer) with
     Pre => I <= C.C;

   procedure Test (I : Positive; E : My_Integer) with
     Ghost;

private

   type My_Array is array (Positive range <>) of My_Integer;

   type Container (C : Natural) is record
      Content : My_Array (1 .. C);
   end record;

   function Get (C : Container; I : Positive) return My_Integer is
      (C.Content (I));

end Use_Types_With_Invariants_No_SPARK;
