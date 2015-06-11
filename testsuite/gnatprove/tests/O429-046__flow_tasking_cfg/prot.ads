package Prot
  with Abstract_State => State,
       Initializes    => (Visible, State)
is
   Visible : Integer := 0;

   protected type P_Int (D : Integer) is
      procedure Get (X : out Integer);

      function Weird_Get (X : Integer) return Integer;

      entry Set (X : Integer);
   private
      The_Protected_Int : Integer := D;
   end P_Int;
end Prot;
