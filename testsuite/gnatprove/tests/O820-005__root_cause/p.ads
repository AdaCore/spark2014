package P is
   type Ar is array (1 .. 10, -1 .. 1) of Natural;
   X : Ar := (others => (others => 0));
   Y : constant Boolean := (for all E of X => E = 0);
   package Q with SPARK_Mode is
      Z : constant Boolean := Y;
      --  Z is not in SPARK due to Y in its declaration and
      --  Y is not in SPARK due to a quantified expression over an array of
      --  dimension 2 (which is greater than 1).
   end Q;
end P;
