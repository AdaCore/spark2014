procedure P with SPARK_Mode is
   function Not_Statically_False return Boolean is (False);

   function F (X : Integer; Y : Integer; Z : Integer) return Boolean is
     (declare
        Dummy : constant Boolean :=
          (if Not_Statically_False then F (1, 1, 1) else True);
      begin
        not F (Y, Z, X)) -- @SUBPROGRAM_VARIANT:FAIL
   with Subprogram_Variant => (Decreases => 0),
     Post => False;

begin
   null;
end P;
