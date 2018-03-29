with Types_With_Invariants_Auto; use Types_With_Invariants_Auto;

package Use_Types_With_Invariants_Auto with SPARK_Mode is

   type Container (C : Natural) is private;

   type Container_Bad (C : Natural) is private;

   function Get (C : Container; I : Positive) return My_Integer with
     Pre => I <= C.C;

   procedure Set (C : in out Container; I : Positive; E : My_Integer) with
     Pre => I <= C.C;

   function Get (C : Container_Bad; I : Positive) return My_Integer_Bad with
     Pre => I <= C.C;

   procedure Set (C : in out Container_Bad; I : Positive; E : My_Integer_Bad)
   with
     Pre => I <= C.C;

   procedure Test (I : Positive; E : My_Integer; F : My_Integer_Bad) with
     Ghost;

private

   type My_Array is array (Positive range <>) of My_Integer;

   type Container (C : Natural) is record
      Content : My_Array (1 .. C);
   end record;

   function Get (C : Container; I : Positive) return My_Integer is
      (C.Content (I));

   type My_Array_Bad is array (Positive range <>) of My_Integer_Bad;

   type Container_Bad (C : Natural) is record
      Content : My_Array_Bad (1 .. C);
   end record;

   function Get (C : Container_Bad; I : Positive) return My_Integer_Bad is
      (C.Content (I));

end Use_Types_With_Invariants_Auto;
