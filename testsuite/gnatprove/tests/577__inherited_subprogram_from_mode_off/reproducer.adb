procedure Reproducer with SPARK_Mode is

   package Nested is
      type Root is tagged record
         F : Integer := 0;
      end record;

      procedure P (X : Root);

      type Child2 is new Root with private;
   private
      pragma SPARK_Mode (Off);

      type Child1 is new Root with record
         G : Integer := 0;
      end record;

      procedure P (X : Child1);

      type Child2 is new Child1 with record
         H : Integer := 0;
      end record;

      procedure P (X : Root) is null;

      procedure P (X : Child1) is null;

   end Nested;
   use Nested;

   X : Child2;
begin
   P (X);
end Reproducer;
