package body P
  with SPARK_Mode => On
is
   procedure Op1 (S : in R;
                  Z : out Boolean)
   is
   begin
      Z := S in R;
   end Op1;

   procedure Op2 (S : in AofR;
                  I : in T;
                  Z : out Boolean)
   is
   begin
      Z := (S (I) in R);
   end Op2;

end P;


