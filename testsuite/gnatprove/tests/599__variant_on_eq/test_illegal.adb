procedure Test_Illegal with SPARK_Mode is
   type OK;
   type OK_Acc is access OK;
   type OK is record
      V : Integer;
      N : OK_Acc;
   end record;

   function "=" (X, Y : OK) return Boolean with
     Subprogram_Variant => (Structural => Y);

   function "=" (X, Y : OK) return Boolean is
     (X.V = Y.V and then (X.N = null) = (Y.N = null)
      and then (if X.N /= null then X.N.all = Y.N.all));

   type Bad;
   type Bad_Acc is access Bad;

   type Bad is record
      V : Integer;
      N : Bad_Acc;
   end record;

   function "=" (X, Y : Bad) return Boolean with
     Subprogram_Variant => (Structural => Y);

   type Holder is record
      C : Bad;
   end record;

   function "=" (X, Y : Bad) return Boolean is
     (X.V = Y.V and then (X.N = null) = (Y.N = null)
      and then (if X.N /= null then X.N.all = Y.N.all)
      and then Holder'(C => X) = Holder'(C => Y));

begin
   null;
end Test_Illegal;
