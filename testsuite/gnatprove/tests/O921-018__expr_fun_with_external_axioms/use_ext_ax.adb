with Ext_Ax; use Ext_Ax;
procedure Use_Ext_Ax with SPARK_Mode is
begin
   pragma Assert (My_Eq (1, 1));
   pragma Assert (not My_Eq (1, 2));
end Use_Ext_Ax;
