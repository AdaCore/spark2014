package body Pack
  with Refined_State => (State1 => (A, B),
                         State2 => (Inner.Inner_Var, Inner.Inner_State))
is
   A, B : Integer;

   procedure Initialize_State is separate
     with Refined_Global => (Output => (A, B)),
          Refined_Depends => ((A, B) => null);

   procedure Double_B is separate
     with Global => (In_Out => B),
          Depends => (B => B);

   package Inner
     with Abstract_State => Inner_State,
          Initializes    => (Inner_State,
                             Inner_Var => Var)
   is
      Inner_Var : Integer;

      procedure Initialize_Inner
        with Global  => (Output => (Inner_State, Inner_Var),
                         Input  => Var),
             Depends => (Inner_State => null,
                         Inner_Var   => Var);
   end Inner;

   package body Inner is separate;
begin
   Initialize_State;
   Double_B;
end Pack;
