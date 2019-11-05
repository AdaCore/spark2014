package body Outer
  with SPARK_Mode,
       Refined_State => (State => (Inner.Inner_State,
                                   Inner.Inner_State_2,
                                   Inner.X,
                                   Inner_2.Y,
                                   Inner_2.Z,
                                   Inner_3.W,
                                   Foo,
                                   Inner.Nested_In_Spec.Nested_In_Spec_Var))
is
   Foo : Integer := 0;

   package Inner
     with Abstract_State => (Inner_State,
                             Inner_State_2),
          Initializes    => (Inner_State_2,
                             Inner_State   => (Init.Var,
                                               Foo),
                             X             => Init.Var,
                             Nested_In_Spec.Nested_In_Spec_Var => Init.Var)
   is
      X : Integer := 0;

      package Nested_In_Spec
        with Initializes => (Nested_In_Spec_Var => Init.Var)
      is
         Nested_In_Spec_Var : Integer := Init.Var;
      end Nested_In_Spec;

      function Get_Inner_State return Integer
        with Global => Inner_State;
   end Inner;

   package Inner_2
     with Initializes => (Y, Z)
   is
      Y, Z : Integer := 0;
   end Inner_2;

   package Inner_3
     with Initializes => W
   is
      W : Integer := 0;
   end Inner_3;

   package Inner_4
     with Initializes => null
   is
      function Add (X, Y : Integer) return Integer is (X + Y);
   end Inner_4;

   package body Inner
     with Refined_State => (Inner_State   => (Y,
                                              Nested_In_Body.Deep_State,
                                              Nested_In_Body.Deep_Var),
                            Inner_State_2 => Z)
   is
      package Nested_In_Body
        with Abstract_State => Deep_State,
             Initializes    => (Deep_State => Init.Var,
                                Deep_Var   => Foo)
      is
         Deep_Var : Integer := Foo;

         function Get_Deep_State return Integer
           with Global => Deep_State;
      end Nested_In_Body;

      Y : Integer;
      Z : Integer;

      package body Nested_In_Body
        with Refined_State => (Deep_State => Deep_Ref)
      is
         Deep_Ref : Integer := Init.Var;

         function Get_Deep_State return Integer is (Deep_Ref)
           with Refined_Global => Deep_Ref;
      end Nested_In_Body;

      function Get_Inner_State return Integer is (Y)
        with Refined_Global => Y;
   begin
      X := X + Init.Var;
      Y := Nested_In_Body.Deep_Var + Nested_In_Body.Get_Deep_State;
      Z := 0;
   end Inner;

end Outer;
