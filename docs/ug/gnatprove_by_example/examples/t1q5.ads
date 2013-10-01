package T1Q5
is
   pragma SPARK_Mode;

   procedure Bounded_Add (X, Y : in Integer; Z : out Integer)
     with Contract_Cases => (Integer'First <= X + Y and X + Y <= Integer'Last => Z = X + Y,
                             Integer'First > X + Y => Z = Integer'First,
                             X + Y > Integer'Last => Z = Integer'Last);

end T1Q5;
