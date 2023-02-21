procedure Infeasible_Abstract with SPARK_Mode is

   package N1 is
      type Root is abstract tagged null record;

      function Bad (X : Root; I : Integer) return Integer is abstract with --@FEASIBLE_POST:FAIL
        Annotate => (GNATprove, Always_Return),
        Post'Class => False;
   end N1;
   use N1;

   function F (X : Root'Class; I : Integer) return Integer with
     Annotate => (GNATprove, Always_Return),
     Post => False;

   function F (X : Root'Class; I : Integer) return Integer is
      C : constant Integer := Bad (X, I);
   begin
      return C;
   end F;

   package N2 is
      type Child1 is new Root with null record;

      function Bad (X : Child1; I : Integer) return Integer;
   end N2;
   use N2;

   package N3 is
      type Child2 is new Root with null record;

      function Bad (X : Child2; I : Integer) return Integer;
   end N3;
   use N3;

   package body N2 is

      function Bad (X : Child1; I : Integer) return Integer is
         C : constant Integer := (if I = 0 then F (Child2'(Root (X) with null record), I) else I);
      begin
         return C;
      end Bad;

   end N2;

   package body N3 is

      function Bad (X : Child2; I : Integer) return Integer is
         C : constant Integer := (if I = 0 then F (Child1'(Root (X) with null record), I) else I);
      begin
         return C;
      end Bad;

   end N3;
begin
   null;
end;
