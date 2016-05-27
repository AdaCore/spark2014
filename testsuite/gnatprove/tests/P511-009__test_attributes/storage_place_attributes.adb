procedure Storage_Place_Attributes
is
   --  pragma SPARK_Mode (On);

   subtype My_Integer is Integer range 1 .. 10;

   type R1 is tagged record
      F1 : Boolean;
   end record;

   type R2 (D1 : My_Integer := 1) is record
      D3 : Integer := 0;
      case D1 is
	 when 5 =>
	    D2 : Boolean := False;
	 when others =>
	    null;
      end case;
   end record;

   subtype SR2 is R2 (5);

   type R3 is record
      E1 : Integer;
   end record;

   subtype R2a is R2(5);
   subtype R2b is R2(1);

   type R2a_array is array (Positive range <>) of R2a;
   pragma Pack (R2a_array);

   R2a_arr : R2a_array (1 .. 3);

   O2a  : R2a;
   O2aa : R2a;
   O2b  : R2b;

   pragma Assert (O2a.D3'First_bit = O2b.D3'First_bit);
   pragma Assert (O2a.D3'First_bit = R2a_arr (1).D3'First_bit);
   pragma Assert (O2a.D3'First_bit = O2a.D3'First_bit);

   O2 : R2;

   pragma Assert (O2.D3'First_Bit = O2a.D3'First_Bit);

   -- FIRST_BIT

   procedure First1 (X : R1) is
   begin
      pragma Assert (X.F1'First_bit >= 0);
   end First1;

   procedure First2 (X : R2) is
   begin
      pragma Assert (X.D1'First_bit >= 0);
   end First2;

   procedure First3 (X : R3) is
   begin
      pragma Assert (X.E1'First_bit >= 0);
   end First3;

   procedure First4 (X : SR2) is
   begin
      pragma Assert (X.D1'First_bit >= 0);
   end First4;

   -- LAST_BIT

   procedure Last1 (X : R1) is
   begin
      pragma Assert (X.F1'First_bit >= 0);
   end Last1;

   procedure Last2 (X : R2) is
   begin
      pragma Assert (X.D1'First_bit >= 0);
   end Last2;

   procedure Last3 (X : R3) is
   begin
      pragma Assert (X.E1'First_bit >= 0);
   end Last3;

   procedure Last4 (X : SR2) is
   begin
      pragma Assert (X.D1'First_bit >= 0);
   end Last4;

   -- POSITION

   procedure Position1 (X : R1) is
   begin
      pragma Assert (X.F1'First_bit >= 0);
   end Position1;

   procedure Position2 (X : R2) is
   begin
      pragma Assert (X.D1'First_bit >= 0);
   end Position2;

   procedure Position3 (X : R3) is
   begin
      pragma Assert (X.E1'First_bit >= 0);
   end Position3;

   procedure Position4 (X : SR2) is
   begin
      pragma Assert (X.D1'First_bit >= 0);
   end Position4;

begin
   null;
end Storage_Place_Attributes;
