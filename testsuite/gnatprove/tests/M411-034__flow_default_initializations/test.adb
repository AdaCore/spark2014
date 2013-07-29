package body Test
is

   V : Integer := 12;
   W : Integer := 666;

   type Def_Int is range 0 .. 100 with Default_Value => 99;

   type Array_A is array (Boolean) of Def_Int;
   type Array_B is array (Boolean) of Integer
     with Default_Component_Value => 123;

   type Rec is record
      A : Integer;
      B : Integer := 42;
      --  C : Integer := V;
      D : Def_Int;
      --  E : Def_Int := Def_Int (V);
      F : Array_A;
      G : Array_B;
   end record;

   type Other_Rec is record
      A : Rec;
      B : Rec := (A => 99,
                  B => 0,
                  --  C => W,
                  D => 0,
                  --  E => 0,
                  F => (others => 0),
                  G => (others => 0));
   end record;

   G : Other_Rec;

   procedure Test_01 (X : out Rec)
   with Global => null,
        Depends => (X => null)
   is
      Tmp : Rec;
   begin
      X := Tmp;
   end Test_01;

   procedure Test_01_B (X : out Other_Rec)
   with Global => null,
        Depends => (X => null)
   is
      Tmp : Other_Rec;
   begin
      Tmp.A.A := 0;
      X := Tmp;
   end Test_01_B;

   procedure Test_02 (X : out Rec)
   with Global => null,
        Depends => (X => null)
   is
      Tmp : Rec;
   begin
      Tmp.A := Integer (Tmp.D);
      X := Tmp;
   end Test_02;

   procedure Test_03 (X : out Def_Int)
   with Global => null,
        Depends => (X => null)
   is
      Tmp : Def_Int;
   begin
      X := Tmp;
   end Test_03;

   procedure Test_04
   with Global => (Output => G),
        Depends => (G => null)
   is
      Tmp : Other_Rec;
   begin
      G := Tmp;
   end Test_04;

   procedure Test_05
   with Global => (In_Out => G),
        Depends => (G => G)
   is
   begin
      G := G;
   end Test_05;

   procedure Test_06 (Secret : Integer;
                      X      : out Integer)
   with Global  => null,
     Depends => (X    => null,
                 null => Secret)
   is
      Tmp : Integer := Secret;

      type T is record
         X : Integer := Tmp; -- NOT ALLOWED
      end record;

      procedure Hide (X : out Integer)
        with Global => Tmp
      is
         Wibble : T;
      begin
         X := Wibble.X;
      end Hide;
   begin
      Tmp := 12;
      Hide (X);
   end Test_06;

end Test;
