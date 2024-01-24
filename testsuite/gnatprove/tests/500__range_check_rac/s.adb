procedure S (LX, HX : Integer) is
   type A is access String;
   type T (L, H : Integer) is record
      C : A (L .. H);
   end record;
   X : T (LX, HX);
begin
   X.C := new String'(LX .. HX => '_'); -- @RANGE_CHECK:FAIL @COUNTEREXAMPLE
end;
