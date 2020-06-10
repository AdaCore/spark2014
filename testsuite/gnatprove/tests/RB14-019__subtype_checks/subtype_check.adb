procedure Subtype_Check with SPARK_Mode is
   type Nat_Array is array (Positive range <>) of Natural with
     Default_Component_Value => 1;
   type Nat_Array_Access is access Nat_Array;

   function Id (X : Integer) return Integer is (X);

   Zero : constant Integer := Id (1);

   subtype Small_Nat_Array is Nat_Array (Zero .. 5);
   type Small_Nat_Array_Access is access Small_Nat_Array;

   subtype Small_Nat_Array_2 is Nat_Array (6 .. 10);

   type R (D : Integer) is record
      F : Integer := 1;
   end record;
   type R_Access is access R;

   procedure Wrong with Pre => True is
      subtype Small_Nat_Array_3 is Nat_Array (Zero .. 10);
      Z : Small_Nat_Array_Access := new Small_Nat_Array_3;--@RANGE_CHECK:FAIL
   begin
      null;
   end Wrong;

   procedure Wrong_2 with Pre => True is
      subtype Even_Nat_Array is Nat_Array with
        Predicate => Even_Nat_Array'Length mod 2 = 0;
      type Even_Nat_Array_Access is access Even_Nat_Array;
      X : Even_Nat_Array_Access := new Small_Nat_Array; --@PREDICATE_CHECK:FAIL
   begin
      null;
   end Wrong_2;

   procedure Wrong_3 with Pre => True is
   Z : Small_Nat_Array_Access := new Small_Nat_Array_2;--@RANGE_CHECK:FAIL
   begin
      null;
   end Wrong_3;

   X : Nat_Array_Access := new Small_Nat_Array;
   X2 : Nat_Array_Access := new Nat_Array (1 .. 5);
   Y : R_Access := new R (10);
begin
   pragma Assert (X.all'First = 1);
   pragma Assert (X2.all'First = 1);
   X (1) := 5;
   X2 (3) := 5;
   pragma Assert (Y.D = Id (10));
   Wrong_2;
end Subtype_Check;
