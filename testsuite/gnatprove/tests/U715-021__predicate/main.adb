procedure Main with SPARK_Mode is

   type T is record
      A : Integer;
      B : Integer;
   end record;

   subtype S is T with Predicate =>
      S.A > 0 and then S.B > 0;

   procedure P (X : T) is
   begin
      pragma Assert (X in S);
   end P;
begin
   null;
end Main;
