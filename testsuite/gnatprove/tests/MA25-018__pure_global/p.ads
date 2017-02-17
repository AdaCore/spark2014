package P
  with SPARK_Mode => On
is
   procedure Op1 (X, Y : in Integer; Z : out Integer)
     with Depends => (Z => (X, Y));

   procedure Op2 (X, Y : in Integer; Z : out Integer)
     with Depends => (Z => (X, Y));

end P;
