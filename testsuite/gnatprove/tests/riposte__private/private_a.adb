package body Private_A with SPARK_Mode
is
   type Optional_Stack is record
      Exists    : Boolean;
      The_Stack : Stack.T;
   end record;

   type Index_T is range 1..1000;
   type Stack_Array is array (Index_T) of Stack.T;

   procedure Test_Complex_A (N   : in     Integer;
                             Dst :    out Complex.T)
     with Depends => (Dst => N),
          Post    => Dst = Complex.Create (N, 0)  --  @POSTCONDITION:PASS
   is
   begin
      Dst := Complex.Create(N, 0);
   end Test_Complex_A;

   procedure Test_Complex_B (N   : in     Integer;
                             Dst :    out Complex.T)
     with Depends => (Dst => N),
          Post    => Dst = Complex.Create (N, 0)  --  @POSTCONDITION:FAIL
   is
   begin
      Dst := Complex.Create(N, 1);
   end Test_Complex_B;

   procedure Test_Complex_C (Foo : in     Complex.T;
                             Dst :    out Complex.T)
     with Depends => (Dst => Foo),
          Post    => Dst = Complex.Create (0, 0)  --  @POSTCONDITION:FAIL
   is
   begin
      Dst := Foo;
   end Test_Complex_C;

   procedure Test_Stack_A (N : in out Integer)
     with Depends => (N => N),
          Post    => N = N'Old  --  @POSTCONDITION:PASS
   is
      S : Stack.T;
   begin
      S := Stack.Create_Stack;
      Stack.Push (S, N);
      N := Stack.Top (S);
   end Test_Stack_A;

   procedure Test_Stack_B (N : in out Integer)
     with Depends => (N => N),
          Post    => N = N'Old  --  @POSTCONDITION:PASS
   is
      S : Optional_Stack;
   begin
      S := Optional_Stack'(Exists    => True,
                           The_Stack => Stack.Create_Stack);
      pragma Assert (S.Exists);  --  @ASSERT:PASS
      Stack.Push (S.The_Stack, N);
      N := Stack.Top (S.The_Stack);
   end Test_Stack_B;

   procedure Test_Stack_C (N : in out Integer)
     with Depends => (N => N),
          Post    => N = N'Old  --  @POSTCONDITION:PASS
   is
      S : Optional_Stack;
   begin
      S := Optional_Stack'(Exists    => True,
                           The_Stack => Stack.Create_Stack);
      pragma Assert (S.Exists);  --  @ASSERT:PASS
      Stack.Push (S.The_Stack, N);
      pragma Assert (Stack.Get_Length (S.The_Stack) = 2);  --  @ASSERT:FAIL
      N := Stack.Top (S.The_Stack);
   end Test_Stack_C;

   procedure Test_Stack_D (Dst :    out Optional_Stack;
                           Src : in     Stack.T)
     with Depends => (Dst => Src),
          Post    =>
            Dst = Optional_Stack'(Exists    => Src = Stack.Null_Stack,
                                  The_Stack => Src)
   is
   begin
      Dst.The_Stack := Src;
      Dst.Exists    := Dst.The_Stack = Stack.Null_Stack;
   end Test_Stack_D;

   --  Arrays of privates.

   procedure Test_Array_A (A : in     Stack_Array;
                           X :    out Stack.T)
     with Depends => (X => A)
   is
   begin
      X := A (5);
      pragma Assert (Stack.Get_Length (X) >= 0);  --  @ASSERT:PASS
   end Test_Array_A;

end Private_A;
