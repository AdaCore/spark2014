package P with SPARK_Mode is

   package ASIL is
      function B (B : Boolean) return Boolean is (B);
      function C (B : Boolean) return Boolean is (B);
      function D return Boolean is (True);
   end ASIL;

   procedure P (X, Y : Integer) with
     Pre =>
       ASIL.D and then
       ASIL.C(X >= 0 and then Y >= 0) and then
       ASIL.B(X < 0) and then
       X / Y = Y / X;

end P;
