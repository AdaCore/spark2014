package body Array_Aggr with SPARK_Mode is
   procedure Bi_Dim_Aggr_OK (One : Natural) is
      subtype My_Positive is Natural range One .. Integer'Last;
      type Nat_Array1 is array (Natural range <>, My_Positive range <>) of Natural;
      type Nat_Array2 is array (My_Positive range <>, Natural range <>) of Natural;
      subtype Nat_Array_12 is Nat_Array1 (1 .. 2, 1 .. 2);
      A : Nat_Array1 (1 .. 2, 1 .. 2) := (3 .. 4 => (3 .. 4 => 0));
      C : Nat_Array_12 := (3 .. 4 => (3 .. 4 => 0));

      procedure Aggregate_KO1 with Pre => One <= 1 is
         D : Nat_Array1 (1 .. 2, 1 .. 2) := (0 .. 1 => (3 .. 4 => 0));
         E : Nat_Array1 (1 .. 2, 1 .. 2) := (3 .. 4 => (0 .. 1 => 0)); --@RANGE_CHECK:FAIL
      begin
         null;
      end Aggregate_KO1;

      procedure Aggregate_KO2 with Pre => One <= 1 is
         B : Nat_Array2 (1 .. 2, 1 .. 2) := (3 .. 4 => (0 .. 1 => 0));
         F : Nat_Array2 (1 .. 2, 1 .. 2) := (0 .. 1 => (3 .. 4 => 0)); --@RANGE_CHECK:FAIL
      begin
         null;
      end Aggregate_KO2;
   begin
      Aggregate_KO1;
      Aggregate_KO2;
   end;
   procedure Bi_Dim_Aggr_KO (One : Natural) is
      subtype My_Positive is Natural range One .. Integer'Last;
      type Nat_Array1 is array (Natural range <>, My_Positive range <>) of Natural;
      type Nat_Array2 is array (My_Positive range <>, Natural range <>) of Natural;

      procedure Subtype_KO with Pre => True is
         subtype Nat_Array_12 is Nat_Array1 (1 .. 2, 1 .. 2); --@RANGE_CHECK:FAIL
      begin
         null;
      end Subtype_Ko;

      procedure Aggregate_KO with Pre => True is
         A : Nat_Array1 (1 .. 2, 1 .. 2) := (3 .. 4 => (3 .. 4 => 0)); --@RANGE_CHECK:FAIL
      begin
         null;
      end Aggregate_KO;
   begin
      Subtype_KO;
      Aggregate_KO;
   end;
end Array_Aggr;
