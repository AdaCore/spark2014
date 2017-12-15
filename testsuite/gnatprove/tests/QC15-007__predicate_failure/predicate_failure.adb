procedure Predicate_Failure is

   subtype Even1 is Integer with Predicate => Even1 mod 2 = 0;
   pragma Predicate_Failure (Even1, "predicate pragma failed");

   subtype Even2 is Integer with Predicate => Even2 mod 2 = 0,
                                 Predicate_Failure => "predicate aspect failed";

   X1 : constant Even1 := 1;
   X2 : constant Even2 := 1;

begin
   null;
end;
