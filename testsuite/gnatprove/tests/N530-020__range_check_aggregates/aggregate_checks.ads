package Aggregate_Checks with SPARK_Mode is
   type Nat_Array is array (Positive range <>) of Natural;

   procedure Do_Wrong_Aggregate (A : Nat_Array) with
     Pre => A'First <= A'Last;
   procedure Do_Wrong_Aggregate_2 (A : Nat_Array) with
     Pre => A'First <= A'Last;
   procedure Do_Wrong_Aggregate_3 (A : Nat_Array) with
     Pre => A'First <= A'Last;
   procedure Do_Wrong_Aggregate_4 (A : Nat_Array) with
     Pre => A'First <= A'Last;
end;
