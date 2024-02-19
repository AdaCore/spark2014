procedure Dispatching_Call_Func with SPARK_Mode is

   package Par is
      type Parent is tagged null record;

      function F (V : Parent) return Boolean;
   end;

   package body Par is
      function F (V : Parent) return Boolean is (True);
   end;
   use Par;

   procedure Foo (V : Parent'Class) with Post => False;

   package Chi is
      type Child is new Parent with record A : Integer; end record;

      overriding
      function F (V : Child) return Boolean with Post => False;
   end;

   package body Chi is
      function F (V : Child) return Boolean is
         A : Parent;
      begin
         Foo (A);
         return True;
      end;
   end;
   use Chi;

   procedure Foo (V : Parent'Class) is
      A : Boolean := F (V);
   begin
      null;
   end Foo;
begin
   null;
end;
