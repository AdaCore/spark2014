package T1Q3B
is
   pragma SPARK_Mode;

   procedure NandGate(P,Q: in Boolean; R: out Boolean)
     with Contract_Cases => (not P and not Q => R,
                             not P and     Q => R,
                                 P and not Q => R,
                                 P and     Q => not R);

end T1Q3B;
