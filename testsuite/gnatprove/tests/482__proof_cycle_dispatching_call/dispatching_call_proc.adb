procedure Dispatching_Call_Proc with SPARK_Mode is

   package Par is
      type Parent is tagged null record;

      procedure F (V : Parent);
   end;

   package body Par is
      procedure F (V : Parent) is null;
   end;
   use Par;

   function Foo (V : Parent'Class) return Boolean with Post => False;

   package Chi is
      type Child is new Parent with record A : Integer; end record;

      overriding
      procedure F (V : Child);
   end;

   package body Chi is
      procedure F (V : Child) is
         A : Parent;
         B : Boolean := Foo (A);
      begin
         null;
      end;
   end;
   use Chi;

   function Foo (V : Parent'Class) return Boolean is
   begin
      F (V);
      return True;
   end Foo;
begin
   null;
end;
