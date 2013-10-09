package body P is
   pragma SPARK_Mode (Off);
   function Get (X : T) return T is
      Tmp : T;
   begin
      Tmp := X;
      return Tmp;
   end Get;
end P;

