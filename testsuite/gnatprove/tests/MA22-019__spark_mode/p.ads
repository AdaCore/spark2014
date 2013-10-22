package P
 with SPARK_Mode
is
  procedure Op (A, B : in Positive; Z : out Character)
    with Depends => (Z => (A, B));

end P;
