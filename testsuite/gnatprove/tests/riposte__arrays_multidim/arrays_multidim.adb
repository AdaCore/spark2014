package body Arrays_Multidim
is
   pragma Warnings (Off, "* has no effect");

   type Byte is mod 2 ** 8;
   type Enum_T is (Elem_0, Elem_1, Elem_2);

   type Map_2D is array (Byte, Byte) of Natural;

   type    Counter is range 0 .. 1002;
   subtype Index   is Counter range 0 .. 1001;
   type    Value   is range -23 .. 69;

   type Two_Dimensional_Array   is array (Index, Index) of Value;
   type Three_Dimensional_Array is array (Index, Index, Index) of Value;

   procedure Test_01 (X : in Map_2D)
     with Depends => (null => X)
   is
   begin
      pragma Assert (X (5, 5) > 1);  --  @ASSERT:FAIL
      null;
   end Test_01;

   procedure Test_02 (X : in out Map_2D)
     with Depends => (X =>+ null)
   is
   begin
      X (5, 5) := 10;
      pragma Assert (X (5, 5) = 10);  --  @ASSERT:PASS
   end Test_02;

   procedure Test_03 (X : in out Map_2D)
     with Depends => (X =>+ null)
   is
   begin
      X (5, 5) := 10;
      pragma Assert (X (5, 5) = 11);  --  @ASSERT:FAIL
   end Test_03;

   procedure Test_04 (X : in Map_2D)
     with Depends => (null => X),
          Pre     => X (5, 5) = 10
   is
   begin
      pragma Assert (X (5, 5) = 11);  --  @ASSERT:FAIL
      null;
   end Test_04;

   procedure Test_05 (X : in out Map_2D)
     with Depends => (X =>+ null),
          Post    => X = X'Old  --  @POSTCONDITION:PASS
   is
   begin
      X := X;
   end Test_05;

   procedure Test_06 (X : in out Map_2D)
     with Depends => (X =>+ null),
          Post    => X = X'Old  --  @POSTCONDITION:PASS
   is
   begin
      X (1, 1) := X (1, 1);
   end Test_06;

   procedure Test_07 (X : in out Map_2D)
     with Depends => (X =>+ null),
          Post    => X (1, 1) in Natural  --  @POSTCONDITION:PASS
   is
   begin
      X := X;
   end Test_07;



   function Tuple_Test
     (Map            : in Map_2D;
      X1, X2, Y1, Y2 : in Byte)
     return Boolean
     with Post => Tuple_Test'Result = True  --  @POSTCONDITION:PASS
   is
   begin
      return X1 /= X2 or Y1 /= Y2 or Map (X1, Y1) = Map (X2, Y2);
   end Tuple_Test;



   -- Multi dimensional arrays, originally from complex_arrays ---

   procedure D2_Element_Access (A    : in Two_Dimensional_Array;
                                I, J : in Index;
                                V    : in Value)
     with Depends => (null => (A, I, J, V)),
          Post    => A(I, J) = V  --  @POSTCONDITION:FAIL
   is
   begin
      null;
   end D2_Element_Access;

   procedure D2_Element_Update_And_Access (A    : in out Two_Dimensional_Array;
                                           I, J : in     Index;
                                           V    : in     Value)
     with Depends => (A =>+ (I, J, V)),
          Post    => A(I, J) = 17  --  @POSTCONDITION:FAIL
   is
   begin
      A(I, J) := V;
   end D2_Element_Update_And_Access;

   procedure D2_Element_Overwrite (A    : in out Two_Dimensional_Array;
                                   I, J : in     Index)
     with Depends => (A =>+ (I, J)),
          Post    => A(I, J) = A(J, I)  --  @POSTCONDITION:FAIL
   is
   begin
      A(I, J) := A(J, I);
      A(I, J) := A(0, 1);
   end D2_Element_Overwrite;

   procedure D2_Element_Passthrough (A    : in out Two_Dimensional_Array;
                                     I, J : in     Index)
     with Depends => (A =>+ (I, J)),
          Pre     => I /= J,
          Post    => A(I, J) /= 23  --  @POSTCONDITION:FAIL
   is
   begin
      A(I, J) := 23;
      A(J, I) := 42;
   end D2_Element_Passthrough;


   procedure D2_Element_Swap (A : in out Two_Dimensional_Array; I, J : Index)
     with Depends => (A =>+ (I, J)),
          Pre     => I /= J,
          Post    => A /= A'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Value;
   begin
      Tmp     := A(I, J);
      A(I, J) := A(J, I);
      A(J, I) := Tmp;
   end D2_Element_Swap;




   procedure D3_Element_Access (A       : in Three_Dimensional_Array;
                                I, J, K : in Index;
                                V       : in Value)
     with Depends => (null => (A, I, J, K, V)),
          Post    => A(I, J, K) = V  --  @POSTCONDITION:FAIL
   is
   begin
      null;
   end D3_Element_Access;

   procedure D3_Element_Update_And_Access
     (A       : in out Three_Dimensional_Array;
      I, J, K : in     Index;
      V       : in Value)
     with Depends => (A =>+ (I, J, K, V)),
          Post    => A(I, J, K) = 17  --  @POSTCONDITION:FAIL
   is
   begin
      A(I, J, K) := V;
   end D3_Element_Update_And_Access;

   procedure D3_Element_Overwrite (A       : in out Three_Dimensional_Array;
                                   I, J, K : in     Index)
     with Depends => (A =>+ (I, J, K)),
          Post    => A(I, J, K) = A(J, I, K)  --  @POSTCONDITION:FAIL
   is
   begin
      A(I, J, K) := A(J, I, K);
      A(I, J, K) := A(0, 1, 2);
   end D3_Element_Overwrite;

   procedure D3_Element_Passthrough (A       : in out Three_Dimensional_Array;
                                     I, J, K : in     Index)
     with Depends => (A =>+ (I, J, K)),
          Pre     => I /= J,
          Post    => A(I, J, K) /= 23  --  @POSTCONDITION:FAIL
   is
   begin
      A(I, J, K) := 23;
      A(J, I, K) := 42;
   end D3_Element_Passthrough;


   procedure D3_Element_Swap (A       : in out Three_Dimensional_Array;
                              I, J, K : in     Index)
     with Depends => (A =>+ (I, J, K)),
          Pre     => I /= J,
          Post    => A /= A'Old  --  @POSTCONDITION:FAIL
   is
      Tmp : Value;
   begin
      Tmp        := A(I, J, K);
      A(I, J, K) := A(J, I, K);
      A(J, I, K) := Tmp;
   end D3_Element_Swap;

   pragma Warnings (On, "* has no effect");
end Arrays_Multidim;
