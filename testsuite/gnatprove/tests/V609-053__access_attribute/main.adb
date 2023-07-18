procedure Main with SPARK_Mode is

   type Int_Acc is access Integer;
   type R is record
      F : Int_Acc;
   end record;
   type P_Acc is access all R;
   type R_Acc is access all R;
   type C_Acc is access constant R;

   type RR is record
      G : R_Acc;
   end record;
   type RR_Acc is access all RR;

   type G_Int is access all Integer;

   X : aliased R := (F => new Integer'(17));--@RESOURCE_LEAK_AT_END_OF_SCOPE:PASS
   A : R_Acc := X'Access;  --@RESOURCE_LEAK_AT_END_OF_SCOPE:PASS
   V : aliased RR := (G => A);  --@RESOURCE_LEAK_AT_END_OF_SCOPE:PASS
   B : RR_Acc := V'Access;  --@RESOURCE_LEAK_AT_END_OF_SCOPE:PASS
   Z : R_Acc := B.G.all'Access;  --@RESOURCE_LEAK_AT_END_OF_SCOPE:FAIL

   M : aliased R := (F => new Integer'(17)); --@RESOURCE_LEAK_AT_END_OF_SCOPE:FAIL
   N : G_Int := M.F.all'Access; --@RESOURCE_LEAK_AT_END_OF_SCOPE:NONE

   C : aliased constant R := (F => new Integer'(17));  --@RESOURCE_LEAK_AT_END_OF_SCOPE:FAIL
   E : C_Acc := C'Access;--@RESOURCE_LEAK_AT_END_OF_SCOPE:NONE

   D : aliased constant R := (F => new Integer'(17));  --@RESOURCE_LEAK_AT_END_OF_SCOPE:FAIL
   F : C_Acc := new R'(D);  --@RESOURCE_LEAK:FAIL
begin
   null;
end Main;
