package PF
with SPARK_Mode
is
   function Prf_Public (I : Integer) return Integer
   with Post => Prf_Public'Result = I / 2;

   function Prf_Hidden (I : Integer) return Integer;

   procedure Test (A : in Integer; B : out Integer)
   with Post => (B = Prf_Public (A) and  B = Prf_Hidden (A));
end PF;
