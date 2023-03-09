package Pack is

   procedure Incr_Glob
     with Global => null,
          Annotate => (Gnatprove, Skip_Proof);
   procedure Incr (X : in out Integer)
      with Annotate => (Gnatprove, Skip_Proof);
   procedure Incr_Full (X : in out Integer);
end Pack;
