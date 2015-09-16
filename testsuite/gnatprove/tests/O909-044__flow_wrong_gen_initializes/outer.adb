package body Outer with SPARK_Mode,
  Refined_State => (Out_State => Inner.In_State)
is
   package body Inner with
     Refined_State => (In_State => Priv) is
   end Inner;
end Outer;
