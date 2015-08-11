package body PO_T
  with Refined_State => (State => Hidden_PO)
is

   protected body P_Int is
      function Get return Integer is
         (if The_Protected_Int >= 0
          then The_Protected_Int
          else The_Protected_Int + 10);

      entry Set (X : Integer) when Condition is
      begin
         The_Protected_Int := X;
      end Set;
   end P_Int;

   protected body Hidden_PO is
      function Get return Integer is
         (if The_Protected_Int >= 0
          then The_Protected_Int
          else The_Protected_Int + 10);

      entry Set (X : Integer) when Switch is
      begin
         The_Protected_Int := X;
      end Set;
   end Hidden_PO;

begin
   P_Int.Set (-10);
   Hidden_Po.Set (-10)
   pragma Assert (P_Int.Get = Hidden_PO.Get);
end PO_T;
