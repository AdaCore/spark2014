with Discrete_Random; use Discrete_Random;

procedure Main
  (Gen     : in out Generator;
   Result1 : out Result_Subtype;
   Result2 : out Result_Subtype)
  with Depends => ((Gen, Result1, Result2) => Gen)
is
begin
   Result1 := Random (Gen);
   Result2 := Random (Gen);
   pragma Assert (Result1 = Result2);  --@ASSERT:FAIL
end;
