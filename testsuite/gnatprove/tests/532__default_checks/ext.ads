package Ext with SPARK_Mode is

   function Rand (X : Integer) return Integer with
     Global => null,
     Import;

   --  DIC check at use

   package P1 is
      package Nested is
         type P is private with Default_Initial_Condition => Rand (1) = 0;
      private
         type P is null record;
      end Nested;

      type R is record
         F : Nested.P; --  @DEFAULT_INITIAL_CONDITION:FAIL
      end record;
   end P1;

   --  Inherited DIC check at use

   package P2 is
      package Nested is
         type Root is tagged private with Default_Initial_Condition => Rand (2) = 0;
         type Child is new Root with private;
      private
         type Root is tagged null record;
         type Child is new Root with null record;
      end Nested;

      type R is record
         F : Nested.Child; --  @DEFAULT_INITIAL_CONDITION:FAIL
      end record;
   end P2;

   --  Array type with default component value

   package P3 is
      subtype My_Pos is Positive range 1 .. Rand (3);

      type A is array (Positive range <>) of My_Pos
        with Default_Component_Value => 3; --  @RANGE_CHECK:FAIL

      type R is record
         F : A (1 .. 10);
      end record;
   end P3;

   --  Array type whose component has a default value

   package P4 is
      type My_Pos is new Positive range 1 .. Rand (4)
        with Default_Value => 4; --  @RANGE_CHECK:FAIL

      type A is array (Positive range 1 .. 10) of My_Pos;

      type R is record
         F : A;
      end record;
   end P4;

   --  Inherited record fields

   package P5 is
      type Root is tagged record
         X : Positive := Rand (5); --  @RANGE_CHECK:FAIL
      end record;

      type R is new Root with record
         Y : Integer;
      end record;
   end P5;

   --  Inherited record fields in private derivation

   package P6 is
      type Root is tagged record
         X : Positive := Rand (6); --  @RANGE_CHECK:FAIL
      end record;

      type R is new Root with private;
   private
      type R is new Root with record
         Y : Integer;
      end record;
   end P6;

   --  Scalar with a default value

   package P7 is
      type My_Pos is new Positive range 1 .. Rand (7)
        with Default_Value => 7; --  @RANGE_CHECK:FAIL
      type R is record
         X : My_Pos;
      end record;
   end P7;

   --  Nested record with a default value

   package P8 is
      type RR is record
         F : Positive := Rand (8); --  @RANGE_CHECK:FAIL
      end record;

      type R is record
         X : RR;
      end record;
   end P8;

   --  Predicate with a reference to a field

   package P9 is
      package Nested is
         type P is private;
         function Get (X : P) return Integer;
      private
         pragma SPARK_Mode (Off);
         type P is record
            F : Integer := 1;
         end record;
         function Get (X : P) return Integer is (X.F);
      end Nested;

      type R is record
         X : Nested.P;
      end record with
        Predicate => Ext.Rand (9) < Nested.Get (X);
   end P9;

   --  Predicate no reference to a field

   package P10 is
      package Nested is
         type P is private;
      private
         pragma SPARK_Mode (Off);
         type P is record
            F : Integer := 1;
         end record;
      end Nested;

      type R is record
         X : Nested.P;
      end record with
        Predicate => Rand (10) > 0;
   end P10;

   --  Nested predicate with a reference to a field

   package P11 is
      package Nested is
         type P is private;
         function Get (X : P) return Integer;
      private
         pragma SPARK_Mode (Off);
         type P is record
            F : Integer := 1;
         end record;
         function Get (X : P) return Integer is (X.F);
      end Nested;

      type RR is record
         Y : Nested.P;
      end record with
        Predicate => Ext.Rand (11) < Nested.Get (Y);

      type R is record
         X : RR; --  @PREDICATE_CHECK_ON_DEFAULT_VALUE:FAIL
      end record;
   end P11;

   --  Nested predicate no reference to a field

   package P12 is
      package Nested is
         type P is private;
      private
         pragma SPARK_Mode (Off);
         type P is record
            F : Integer := 1;
         end record;
      end Nested;

      type RR is record
         Y : Nested.P;
      end record with
        Predicate => Ext.Rand (12) > 0;

      type R is record
         X : RR; --  @PREDICATE_CHECK_ON_DEFAULT_VALUE:FAIL
      end record;
   end P12;

   --  Defaulted discriminants

   package P13 is
      type My_Pos is new Positive range 1 .. Rand (13);

      type RR (D : My_Pos:= 13) is record --  @RANGE_CHECK:FAIL
         Y : Integer;
      end record;

      type R is record
         X : RR;
      end record;
   end P13;

   --  Defaulted discriminants on private

   package P14 is
      type My_Pos is new Positive range 1 .. Rand (14);

      package Nested is
         type P (D : My_Pos := 14) is private; --  @RANGE_CHECK:FAIL
      private
         pragma SPARK_Mode (Off);
         type P (D : My_Pos := 14) is record
            F : Integer := 1;
         end record;
      end Nested;

      type R is record
         X : Nested.P;
      end record;
   end P14;


end Ext;
