package Raise_Statements
  with Initializes => G
is
   G  : Integer := 0;
   G2 : Integer := 0;

   procedure Returning_Proc
     with Global => (In_Out => G);

   procedure Non_Returning_Proc (Par : Integer)
     with No_Return,
          Exceptional_Cases => (others => False),
          Global => (Output => G);

   procedure OK_1 (Par1 : in out Integer;
                   Par2 : in     Integer)
     with Pre    => Par2 = 3,
          Global => null;

   procedure OK_2 (Par : Integer)
     with Global => (In_Out => G);

   procedure OK_3 (OK : Boolean)
     with Global => (In_Out => G),
          Pre    => OK;
end Raise_Statements;
