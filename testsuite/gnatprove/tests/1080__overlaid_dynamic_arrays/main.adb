procedure Main (C : Integer) with SPARK_Mode is
   type Int_8 is mod 256 with Size => 8;
   type Byte_Array is array (Positive range <>) of aliased Int_8;
   subtype SC is Byte_Array (1 .. C);
   subtype S4 is Byte_Array (1 .. 4);

   procedure P1 (X : SC) with
     Pre => C = 4;

   procedure P1 (X : SC) is
      Y : aliased constant S4
      with
        Import,
        Address   => X'Address,
        Alignment => 8;
   begin
      null;
   end P1;

   procedure P2 (X : S4) with
     Pre => C = 4;

   procedure P2 (X : S4) is
      Y : aliased constant SC
      with
        Import,
        Address   => X'Address,
        Alignment => 8;
   begin
      null;
   end P2;

   procedure P3 (X : SC);

   procedure P3 (X : SC) is
      Y : aliased constant S4
      with
        Import,
        Address   => X'Address,
        Alignment => 8;
   begin
      null;
   end P3;

   procedure P4 (X : S4);

   procedure P4 (X : S4) is
      Y : aliased constant SC
      with Import, Address => X'Address, Alignment => 8;
   begin
      null;
   end P4;

   type Byte_Matrix is array (Positive range <>, Positive range <>) of aliased Int_8;
   subtype AC is Byte_Matrix (1 .. C, 1 .. C);
   subtype A4 is Byte_Matrix (1 .. 4, 1 .. 4);

   procedure P5 (X : AC) with
     Pre => C = 4;

   procedure P5 (X : AC) is
      Y : aliased constant A4
      with
        Import,
        Address   => X'Address,
        Alignment => 8;
   begin
      null;
   end P5;

   procedure P6 (X : A4) with
     Pre => C = 4;

   procedure P6 (X : A4) is
      Y : aliased constant AC
      with
        Import,
        Address   => X'Address,
        Alignment => 8;
   begin
      null;
   end P6;

   procedure P7 (X : AC);

   procedure P7 (X : AC) is
      Y : aliased constant A4
      with
        Import,
        Address   => X'Address,
        Alignment => 8;
   begin
      null;
   end P7;

   procedure P8 (X : A4);

   procedure P8 (X : A4) is
      Y : aliased constant AC
      with Import, Address => X'Address, Alignment => 8;
   begin
      null;
   end P8;

   --  Type without aliased components, the size of the array is not the number
   --  of elements times the size of the element as there are gaps at the end.

   type Bool_Array is array (Positive range <>) of Boolean with Pack;
   subtype BC is Bool_Array (1 .. C);
   type B4 is new Bool_Array (1 .. 4) with Size => 4, Object_Size => 8, Pack;

   procedure P9 (X : BC) with
     Pre => C = 4;

   procedure P9 (X : BC) is
      Y : aliased constant B4
      with Import, Address => X'Address, Alignment => 8;
   begin
      null;
   end P9;

   --  We don't handle arrays whose component size is dynamic for now

   type AA is array (Integer range <>) of aliased AC;
   subtype SAA is AA (1 .. 1);

   procedure P10 (X : in out SAA) with
     Pre => C = 4;

   procedure P10 (X : in out SAA) is
      Y : aliased S4
      with
        Import,
        Address   => X'Address,
        Alignment => 8;
   begin
      null;
   end P10;

   procedure P11 (X :in out  AA) with
     Pre => C = 4;

   procedure P11 (X :in out  AA) is
      Y : aliased S4
      with
        Import,
        Address   => X (1 .. 1)'Address,
        Alignment => 8;
   begin
      null;
   end P11;

begin
   null;
end Main;
