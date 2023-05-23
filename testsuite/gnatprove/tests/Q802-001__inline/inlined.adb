package body Inlined with SPARK_Mode is
   function F_2 (X : Integer) return Integer is
   begin
      return X;
   end F_2;

   function F_3 (X : Integer) return Integer is
   begin
      return 0;
   end F_3;

   function F_4 (X : T) return T is
   begin
      return X;
   end F_4;
end Inlined;
