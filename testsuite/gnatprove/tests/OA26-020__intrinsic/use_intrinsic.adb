with Import_Intrinsic; use Import_Intrinsic;
procedure Use_Intrinsic is
   X : New_Float := Create (0.0);
   Y : New_Float := Create (42.0);
begin
   pragma Assert (X < Y);  --  @ASSERT:PASS
   pragma Assert (Y < X);  --  @ASSERT:FAIL
end;
