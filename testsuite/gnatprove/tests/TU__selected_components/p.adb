package body P
  with SPARK_Mode => On
is
   function GRTF2 (X : in RT) return Integer is
   begin
      return X.F2; -- error
   end GRTF2;

   function GRTF3 (X : in RT) return Float is
   begin
      return X.F3; -- OK
   end GRTF3;

   function GRFF2 (X : in RF) return Integer is
   begin
      return X.F2; -- OK
   end GRFF2;


   function GRFF3 (X : in RF) return Float is
   begin
      return X.F3; -- error
   end GRFF3;

end P;
