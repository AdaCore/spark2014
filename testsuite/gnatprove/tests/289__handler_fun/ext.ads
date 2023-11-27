package Ext with SPARK_Mode is
   Counter : Natural := 0 with Atomic;

   type Handler_Fun is access function return Integer with
     Annotate => (GNATprove, Handler);

   function Reset return Integer with Side_Effects, Volatile_Function;

   C : constant Handler_Fun := Reset'Access;
end Ext;
