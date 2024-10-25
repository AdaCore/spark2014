procedure Main with SPARK_Mode is
   package A is
      type I is interface;
      function F (X : I) return Boolean is abstract;
      procedure P (X : I) is abstract with Pre'Class => F (X), Post'Class => False;
      type J is interface and I;
      procedure P (X : J) is abstract with Pre'Class => F (X), Post'Class => True;
   end A;
begin
   null;
end Main;
