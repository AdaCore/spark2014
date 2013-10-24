package Hidden_Liar
  with SPARK_Mode
is
   procedure Add (X, Y : in     Integer;
                  Z    :    out Integer)
     with Global  => null,
          Depends => (Z => (X, Y));
end Hidden_Liar;
