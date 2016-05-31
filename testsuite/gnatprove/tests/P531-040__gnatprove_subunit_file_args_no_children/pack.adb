package body Pack
   with SPARK_Mode => On
is

   function Foo (P: Point_T) return Boolean is
   begin
      return P.X > P.Y;
   end Foo;

   procedure Proc (R : in Exp_Seq_T; I: in Idx_T; Nf: out Opt_P_T)
     is
     separate
     with Global => null;

end Pack;
