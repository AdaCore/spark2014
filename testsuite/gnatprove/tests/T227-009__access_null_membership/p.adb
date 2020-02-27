procedure P is
   type T is access Integer;
   subtype S is not null T;  --  a null-excluding subtype
   Y : T := null;            --  a null value
begin
   pragma Assert (Y in S);   --  @ASSERT:FAIL
end P;
