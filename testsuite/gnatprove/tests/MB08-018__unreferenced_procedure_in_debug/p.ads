package P
  with SPARK_Mode => On
is
   procedure Inc_And_Log (X : in out Integer)
     with Depends => (X => X),
          Pre     => X < Integer'Last,
          Post    => X = X'Old + 1;

end P;
