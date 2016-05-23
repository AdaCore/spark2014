package body Alignment_Attribute
is
   pragma SPARK_Mode (On);

   subtype My_Integer is Integer range 1 .. 10;

   type R1 is null record;

   type R2 (D1 : My_Integer := 1) is record
      case D1 is
	 when 5 =>
	    D2 : Boolean;
	 when others =>
	    null;
      end case;
   end record;

   subtype SR2 is R2 (5);

   type R3 is tagged record
      I : Integer;
   end record;

   type R4 is new R3 with
      record
	 J : Integer;
      end record;

   type Constr_Array is array (My_Integer) of Positive;
   type Unconstr_Array is array (Positive range <>) of Natural;

   B : Boolean := True;
   Int : constant Integer := 2;
   S : String := "test";

   M : My_Integer := My_Integer'Last;

   RT1  : R1;
   RT2  : R2 (3);
   RST2 : SR2;
   RT3  : R3;
   RT4  : R4;

   CA : Constr_Array := (others => 2);
   UA : Unconstr_Array (1 .. 10) := (others => 1);

   procedure P (CA : in out Constr_Array) is
   begin
      CA := CA;
      pragma Assert (CA'Alignment >= 0);
   end P;

   procedure Q (X : Integer) is
      type Array1 is array (1 .. X) of Integer;
      type Array2 is array (1 .. 1) of Array1;
      A1 : Array1 := (others => 1);
      A2 : Array2 := (others => A1);
   begin
      pragma Assert (A2'Alignment >= 0);
      pragma Assert (A2'Alignment < 0); -- @ASSERT:FAIL
   end Q;

begin

   -- Types
   pragma Assert (R1'Alignment >= 0);
   pragma Assert (R2'Alignment >= 0);
   pragma Assert (SR2'Alignment >= 0);
   pragma Assert (R3'Alignment >= 0);
   pragma Assert (R4'Alignment >= 0);
   pragma Assert (My_Integer'Alignment >= 0);
   pragma Assert (Boolean'Alignment >= 0);
   pragma Assert (Integer'Alignment >= 0);
   pragma Assert (String'Alignment >= 0);
   pragma Assert (Constr_Array'Alignment >= 0);
   pragma Assert (Unconstr_Array'Alignment >= 0);

   -- Objects

   pragma Assert (S'Alignment >= 0);
   pragma Assert (M'Alignment >= 0);
   pragma Assert (B'Alignment >= 0);
   pragma Assert (Int'Alignment >= 0);
   pragma Assert (RT1'Alignment >= 0);
   pragma Assert (RT2'Alignment >= 0);
   pragma Assert (RST2'Alignment >= 0);
   pragma Assert (RT3'Alignment >= 0);
   pragma Assert (RT4'Alignment >= 0);
   pragma Assert (CA'Alignment >= 0);
   pragma Assert (UA'Alignment >= 0);

end Alignment_Attribute;
