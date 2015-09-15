package C with
   SPARK_Mode,
   Abstract_State => (State with External)
is
   procedure Read
       (Value    :    out Integer)
   with
      Global  => (In_Out => State),
      Depends => ((Value, State) => State);

   procedure Is_Positive (Result   :    out Boolean);
end C;
