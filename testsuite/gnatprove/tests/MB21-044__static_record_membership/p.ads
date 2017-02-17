package P
  with SPARK_Mode => On
is
   type R is record
      F1 : Integer;
      F2 : Boolean;
   end record;

   type T is range 1 .. 10;

   type AofR is array (T) of R;

   procedure Op1 (S : in R;
                  Z : out Boolean)
     with Post => Z = (S in R);

   procedure Op2 (S : in AofR;
                  I : in T;
                  Z : out Boolean)
     with Post => Z = (S (I) in R);

end P;


