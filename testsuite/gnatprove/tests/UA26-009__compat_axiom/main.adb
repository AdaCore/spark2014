with Ext; use Ext;
procedure Main with SPARK_Mode is
   C : Grand_Child := (1, 2, 3);
   CC : Grand_Child'Class := C;
begin
   pragma Assert (CC.Get = 3);
end;
