package body Uninitialized
  with SPARK_Mode,
       Refined_State => (State => Var)
is
   Var : Natural;

   procedure Set (Par : in Natural)
     with Refined_Global => (Output => Var)
   is
   begin
      Var := Par;
   end Set;
end Uninitialized;
