with Ext; use Ext;
procedure Main with SPARK_Mode is
   X : T1_Acc := Create;
begin
   Update (X);
   Dealloc (X);
end Main;
