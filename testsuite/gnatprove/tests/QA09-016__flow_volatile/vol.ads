package Vol with SPARK_Mode is
   pragma Elaborate_Body;
   type T is record
      C : Integer;
   end record
     with Volatile;
   G : T with Async_Writers;
   H : Integer;
   function Ident (X : T) return Integer with Volatile_Function;
end Vol;
