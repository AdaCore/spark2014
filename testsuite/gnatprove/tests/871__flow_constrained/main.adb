procedure Main with SPARK_Mode is
   type Nested (B : Boolean := False) is record
      null;
   end record;

   type Rec (B : Boolean := False) is record
      case B is
         when True =>
            N : Nested;
         when others =>
            null;
      end case;
   end record;

   procedure Foo (R : out Rec) with Pre => not R'Constrained;

   procedure Foo (R : out Rec) is null;

begin
   null;
end Main;
