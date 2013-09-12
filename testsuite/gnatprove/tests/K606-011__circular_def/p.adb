procedure P is
   pragma SPARK_Mode (Off);
   type r1(d1 : integer);
   type r2(d2 : integer);

   type acc_r1 is access r1;
   type acc_r2 is access r2;

   type r1(d1 : integer) is
      record
         c1 : acc_r2(d1);
      end record;

   type r2(d2 : integer) is
      record
         c2 : acc_r1(d2);
      end record;

begin
   null;
end P;
