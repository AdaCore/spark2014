procedure Illegal_Annot with SPARK_Mode is

   --  Missing 3rd parameter

   package P1 is
      type T is private with
        Annotate => (GNATprove, Predefined_Equality);
   private
      pragma SPARK_Mode (Off);
      type T is access Integer;
   end P1;

   --  Unexpected entity kind

   package P2 is
      procedure P with
        Annotate => (GNATprove, Predefined_Equality, "No_Equality");
   private
      pragma SPARK_Mode (Off);
      procedure P is null;
   end P2;

   --  Unexpected 3rd parameter kind

   package P3 is
      type T is private with
        Annotate => (GNATprove, Predefined_Equality, 4);
   private
      pragma SPARK_Mode (Off);
      type T is access Integer;
   end P3;

   --  Unexpected 3rd parameter on type

   package P4 is
      type T is private with
        Annotate => (GNATprove, Predefined_Equality, "No_Equal");
   private
      pragma SPARK_Mode (Off);
      type T is access Integer;
   end P4;

   --  Unexpected 3rd parameter on constant

   package P5 is
      type T is private with
        Annotate => (GNATprove, Predefined_Equality, "Only_Null");
      C : constant T with
        Annotate => (GNATprove, Predefined_Equality, "Null");
   private
      pragma SPARK_Mode (Off);
      type T is access Integer;
      C : constant T := null;
   end P5;

   --  Non private type

   package P6 is
      type T is private with
        Annotate => (GNATprove, Predefined_Equality, "No_Equality");
   private
      type T is access Integer;
   end P6;

   --  Tagged type with only_null

   package P7 is
      type T is tagged private with
        Annotate => (GNATprove, Predefined_Equality, "Only_Null");
      C : constant T with
        Annotate => (GNATprove, Predefined_Equality, "Null_Value");
   private
      pragma SPARK_Mode (Off);
      type Int_Acc is access Integer;
      type T is tagged record
         F : Int_Acc;
      end record;
      C : constant T := (F => null);
   end P7;

   --  Misplaced annotation on type

   package P8 is
      type T is private;
      procedure P is null;
      pragma Annotate (GNATprove, Predefined_Equality, "No_Equality", T);
   private
      pragma SPARK_Mode (Off);
      type T is access Integer;
   end P8;

   --  Misplaced annotation on constant

   package P9 is
      type T is private with
        Annotate => (GNATprove, Predefined_Equality, "Only_Null");
      C : constant T;
      procedure P is null;
      pragma Annotate (GNATprove, Predefined_Equality, "Null_Value", C);
   private
      pragma SPARK_Mode (Off);
      type T is access Integer;
      C : constant T := null;
   end P9;

   --  Misplaced constant

   package P10 is
      package Nested is
         type T is private with
           Annotate => (GNATprove, Predefined_Equality, "Only_Null");
         N : constant T;
      private
         pragma SPARK_Mode (Off);
         type T is access Integer;
         N : constant T := null;
      end Nested;
      C : constant Nested.T := Nested.N with
        Annotate => (GNATprove, Predefined_Equality, "Null_Value");
   end P10;

   --  Missing null value with only_null. Add other annotate pragmas that will
   --  be traversed while looking for the null value.

   package P11 is
      type T is private with
        Annotate => (GNATprove, Predefined_Equality, "Only_Null");
      function F (X, Y : T) return Boolean with
	Annotate => (GNATprove, Logical_Equal);
      type T2 is private with
        Annotate => (GNATprove, Ownership, "Needs_Reclamation"),
        Annotate => (GNATprove, Predefined_Equality, "Only_Null");
      C : constant T2 with
        Annotate => (GNATprove, Ownership, "Reclaimed_Value"),
        Annotate => (GNATprove, Predefined_Equality, "Null_Value");
   private
      pragma SPARK_Mode (Off);
      type T is access Integer;
      function F (X, Y : T) return Boolean is (X = Y);
      type T2 is access Integer;
      C : constant T2 := null;
   end P11;

   --  Null value without predefined equality on type

   package P12 is
      type T is private;
      C : constant T with
        Annotate => (GNATprove, Predefined_Equality, "Null_Value");
   private
      pragma SPARK_Mode (Off);
      type T is access Integer;
      C : constant T := null;
   end P12;

   --  Null value with No_Equality

   package P13 is
      type T is private with
        Annotate => (GNATprove, Predefined_Equality, "No_Equality");
      C : constant T with
        Annotate => (GNATprove, Predefined_Equality, "Null_Value");
   private
      pragma SPARK_Mode (Off);
      type T is access Integer;
      C : constant T := null;
   end P13;

   --  Duplicated null value

   package P14 is
      type T is private with
        Annotate => (GNATprove, Predefined_Equality, "Only_Null");
      C : constant T with
        Annotate => (GNATprove, Predefined_Equality, "Null_Value");
      D : constant T with
        Annotate => (GNATprove, Predefined_Equality, "Null_Value");
   private
      pragma SPARK_Mode (Off);
      type T is access Integer;
      C : constant T := null;
      D : constant T := null;
   end P14;

   --  Duplicated annotations on type

   package P15 is
      type T is private with
        Annotate => (GNATprove, Predefined_Equality, "No_Equality");
      pragma Annotate (GNATprove, Predefined_Equality, "Only_Null", T);
   private
      pragma SPARK_Mode (Off);
      type T is access Integer;
   end P15;

   --  Duplicated annotations on constants

   package P16 is
      type T is private with
        Annotate => (GNATprove, Predefined_Equality, "Only_Null");
      C : constant T with
        Annotate => (GNATprove, Predefined_Equality, "Null_Value");
      pragma Annotate (GNATprove, Predefined_Equality, "Null_Value", C);
   private
      pragma SPARK_Mode (Off);
      type T is access Integer;
      C : constant T := null;
   end P16;

   --  Annotation is ignored on entities with mode Off

   package P17 is
      procedure P with
	SPARK_Mode => Off,
        Annotate => (GNATprove, Predefined_Equality, "Only_Null");
      procedure P is null with SPARK_Mode => Off;
   end P17;
begin
   null;
end;
