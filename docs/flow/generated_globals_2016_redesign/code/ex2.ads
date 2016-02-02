package Ex2 with
   Abstract_State => State
is
   procedure P0 with
      Global => (In_Out => State);

   procedure P2 with
      Global => (In_Out => State);

   procedure P3 with
      Global => (In_Out => State);

end Ex2;
