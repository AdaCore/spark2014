package Ext is
   type T is private;

   C : aliased Integer := 15;

   function F return T with SPARK_Mode;
private
   type T is access all Integer;

   function F return T is (C'Access) with SPARK_Mode; -- Bad: 'Access on private type
end Ext;
