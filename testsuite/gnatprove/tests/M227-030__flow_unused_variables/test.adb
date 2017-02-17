package body Test is

   State : Integer;
   Other : Integer;
   --  Other is not used.

   procedure Test_01 (A : Integer;
                      B : out Integer;
                      C : in out Integer)
   is
   begin
      B := 12;
      --  A is unused.
      --  C is unused.
   end Test_01;

   procedure Test_02 (A : Integer;
                      B : out Integer)
   with Global => State;

   procedure Test_02 (A : Integer;
                      B : out Integer)
   is
   begin
      B := A;
      --  State is not used.
   end Test_02;

   procedure Test_03 (A : Integer;
                      B : out Integer)
   with Global => (In_Out => State);

   procedure Test_03 (A : Integer;
                      B : out Integer)
   is
   begin
      B := A;
      --  State is not set
   end Test_03;

   procedure Test_04 (A : Integer;
                      B : out Integer)
   is
   begin
      B := 12;
      --  A is not used
   end Test_04;

   procedure Test_05 (A : Integer;
                      B : out Integer)
   is
      L : Integer;
   begin
      B := A;
      --  L is not used.
   end Test_05;

   procedure Test_06 (A : Integer;
                      B : out Integer)
   is
      L : Integer := 10;
   begin
      B := A;
      --  L is not used.
   end Test_06;

end Test;
