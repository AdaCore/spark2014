package P is
   type T is private;
   function Get (X : T) return T with
     Post => Get'Result = X;
private
   pragma SPARK_Mode (Off);
   type T is access Integer;
end P;

