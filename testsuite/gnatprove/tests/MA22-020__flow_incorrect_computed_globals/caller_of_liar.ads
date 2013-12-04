package Caller_Of_Liar
  with SPARK_Mode
is
   procedure Add_Three (X, Y, Z : in     Integer;
                        T       :    out Integer)
     with Global => null,
          Depends => (T => (X, Y, Z));
end Caller_Of_Liar;
