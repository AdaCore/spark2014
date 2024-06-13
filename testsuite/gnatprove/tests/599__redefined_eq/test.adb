procedure Test with SPARK_Mode is

   type OK_2;
   type OK_2_Acc is access OK_2;
   type OK_2 is record
      V : Integer;
      N : OK_2_Acc;
   end record;

   function "=" (X, Y : OK_2) return Boolean;

   function Eq (X, Y : OK_2) return Boolean with
     Subprogram_Variant => (Structural => Y);

   function Eq (X, Y : OK_2) return Boolean is
     (X.V = Y.V and then (X.N = null) = (Y.N = null)
      and then (if X.N /= null then Eq (X.N.all, Y.N.all)));

   function "=" (X, Y : OK_2) return Boolean is (Eq (X, Y));

begin
   null;
end Test;
