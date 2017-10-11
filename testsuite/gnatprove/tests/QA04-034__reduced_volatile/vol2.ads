package Vol2 with SPARK_Mode is
   pragma Elaborate_Body;
   type T is record
      C : Integer;
   end record
     with Volatile;
   type A is array (1 .. 2) of T;
   G : A with Async_Readers, Async_Writers;
   H1, H2 : Integer;
   procedure Ident (X : T; Result : out Integer);
end Vol2;
