package body Test
is

   function Double (X : in Natural) return Natural
   is
   begin
      return X * 2;
   end Double;

   procedure Tons_Of_Types (N : Integer)
   is
      Good_Constant : constant := 12;
      Bad_Constant  : constant Integer := N;
      Ugly_Constant : constant Integer := Double (8);

      type Derived_Int is new Integer range 5 .. Good_Constant;
      --  A full type declaration.

      --  type Derived_Int_I is new Integer
      --    range 5 .. 12 with Default_Value => 7;
      --  A full type declaration with an initialization.

      type Static_Array_T   is array (1 .. Good_Constant) of Boolean;
      type Dyn_Array_T      is array (1 .. Bad_Constant) of Boolean;
      type Manifest_Array_T is array (1 .. Ugly_Constant) of Boolean;

      --  subtype Entire_Subtype_Int is Integer;
      --  --  N_Subtype_Declaration

      procedure Nested
      is
         type Static_Array_T   is array (1 .. Good_Constant) of Boolean;
         type Dyn_Array_T      is array (1 .. Bad_Constant) of Boolean;
         type Manifest_Array_T is array (1 .. Ugly_Constant) of Boolean;
      begin
         null;
      end Nested;

   begin
      null;
   end Tons_Of_Types;

   procedure Test_01 (S : String;
                      L : out Natural)
   is
   begin
      L := S'Length;
   end Test_01;

   ----------------------------------------------------------------------
   --  Issues when we do not deal with dynamic types and constants
   ----------------------------------------------------------------------

   procedure Issue_01 (A : Integer;
                       B : out Integer)
   with Global => null,
        Depends => (B => A)
   is
      Tmp : constant Integer := A;
   begin
      B := Tmp;
      --  We get two errors: that A is not used and B does not depend
      --  on A.
   end Issue_01;

   procedure Issue_02 (A : Integer;
                       B : out Integer)
   with Global => null,
        Depends => (B => A)
   is
      subtype Tmp is Integer range A .. A;
   begin
      B := Tmp'First;
      --  Same as above, but with a type.
   end Issue_02;

   procedure Issue_03 (S : out String)
   with Global => null
   is
   begin
      S := (others => ' ');
      --  Dependence on S is not captured.
   end Issue_03;

   procedure Issue_04 (A : out Integer)
   with Global => null,
        Depends => (A => null)
   is
      Tmp : constant Integer := A;
      --  We now do detect the use of A here, so that is OK.
   begin
      A := Tmp;
   end Issue_04;

   procedure Issue_05 (A : out Integer)
   with Global => null,
        Depends => (A => null)
   is
      subtype Tmp is Integer range A .. A;
   begin
      A := Tmp'First;
   end Issue_05;


end Test;
