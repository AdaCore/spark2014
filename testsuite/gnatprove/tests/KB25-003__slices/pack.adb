package body Pack is

   Glob   : String := "qwertyuiopasdfghjklzxcvbnm";
   G      : String (1 .. 4) := Glob (1 .. 4);

   type Arr1 is array (Natural range <>)  of Integer;
   type Arr2 is array (Natural range <>, Natural range <>)  of Integer;

   Matrix : Arr2 := (1 .. 4 => (1 .. 4 => 1));

   procedure A1 is
      My_S1 : String (1 .. 4) := (1 .. 4 => Glob (1));
      My_A  : constant Arr1 (1 .. 4) := (others => 42);
      My_B  : constant Arr1 (1 .. 4) := My_A (1 .. 4);
   begin
      pragma Assert (My_A = (1 .. 4 => 42));
      pragma Assert (My_B = (1 .. 4 => 42));
      pragma Assert (My_B /= (1 .. 4 => 42)); --  @ASSERT:FAIL
      null;
   end A1;

   procedure A2 is
      My_S2 : String (1 .. 4) := Glob (1 .. 4);
      My_A  : constant Arr1 (1 .. 4) := (others => 42);
      My_B  : constant Arr1 (1 .. 4) := My_A (1 .. 4);
   begin
      pragma Assert (My_S2 (1 .. 3) = Glob (1 .. 3));
      pragma Assert (My_B = My_A (1 .. 4));
      pragma Assert (My_S2 (1 .. 3) /= Glob (1 .. 3)); --  @ASSERT:FAIL
      null;
   end A2;

   procedure AN21 is
      My_S2 : String (1 .. 4) := Glob (1 .. 4);
      My_A  : constant Arr1 (1 .. 4) := (others => 42);
      My_B  : constant Arr1 (1 .. 4) := My_A (1 .. 4);
   begin
      pragma Assert (My_S2 (1 .. 3) = Glob (1 .. 3));
      pragma Assert (My_S2 (1 .. 3) /= Glob (1 .. 3)); --  @ASSERT:FAIL
      null;
   end AN21;

   procedure AN22 is
      My_S2 : String (1 .. 4) := Glob (1 .. 4);
      My_A  : constant Arr1 (1 .. 4) := (others => 42);
      My_B  : constant Arr1 (1 .. 4) := My_A (1 .. 4);
   begin
      pragma Assert (My_S2 (1 .. 3) = Glob (1 .. 3));
      pragma Assert (My_S2 (1 .. 3) /= Glob (1 .. 3)); --  @ASSERT:FAIL
      null;
   end AN22;

   procedure A3 is
      My_S3 : String (1 .. 4) := Glob (2 .. 5);
   begin
      null;
   end A3;

   procedure A4 is
      My_S4 : String (1 .. 4) := (others => ' ');
   begin
      null;
      My_S4 (1 .. 4) := G;
      pragma Assert (My_S4 (2) = G (2));
      pragma Assert (My_S4 (2) /= G (2)); --  @ASSERT:FAIL
      My_S4 (2 .. 3) := Glob (2 .. 3);
   end A4;

   procedure A11 is
      My_S111 : String (3 .. 6) := (others => 'A');
      My_S112 : String (2 .. 5) := My_S111;
   begin
      null;
   end A11;

   procedure Init (A : out Arr1)
     with Post => (for all J in A'Range => A (J) = 1);

   procedure Init (A : out Arr1) is
   begin
      A := (others => 1);
   end Init;

   procedure P is
      A : Arr1 (7 .. 10);
   begin
      Init (A);
      pragma Assert (A (8) = 1);
      pragma Assert (A (9) = 2); --  @ASSERT:FAIL
   end P;

end Pack;
