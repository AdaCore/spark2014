procedure Main with SPARK_Mode is

   function F1 (X : Integer) return Integer is (X)
     with Annotate => (GNATprove, Always_Return);

   procedure P1 (X : out Integer) with
     Annotate => (GNATprove, Always_Return)
   is
   begin
      X := 0;
   end P1;

   package Nested_1 with
     Annotate => (GNATprove, Always_Return)
   is
   end Nested_1;

   function F2 (X : Integer) return Integer is (X);
   pragma Annotate (GNATprove, Always_Return, F2);

   procedure P2 (X : out Integer)
   is
   begin
      X := 0;
   end P2;
   pragma Annotate (GNATprove, Always_Return, P2);

   package Nested_2 is
      pragma Annotate (GNATprove, Always_Return);
   end Nested_2;
begin
   null;
end Main;
