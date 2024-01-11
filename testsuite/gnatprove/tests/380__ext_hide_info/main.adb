with Ext;

procedure Main with SPARK_Mode is

   function Id (X : Integer) return Integer is (Ext.Id_2 (X));

begin
   null;
end Main;
