private package Base.A.B with
   Abstract_State =>
     ((State        with           Part_Of => Base.A.State),
      (Atomic_State with External, Part_Of => Base.A.Atomic_State)),
   Elaborate_Body,
   SPARK_Mode
is
end Base.A.B;
