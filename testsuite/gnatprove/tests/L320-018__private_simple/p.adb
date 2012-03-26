package body P is
   function Get (X : T) return T is
      Tmp : T;
   begin
      Tmp := X;
      return Tmp;
   end Get;
end P;

