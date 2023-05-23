procedure Main2 is
   type T is access function (X : Integer) return Integer;

   function F1 (X : Integer) return Integer with
     Post => False, --@ POSTCONDITION:FAIL
     Annotate => (GNATprove, Always_Return);

   function F2 (X : Integer) return Integer with
     Post => False, --@ POSTCONDITION:FAIL
     Annotate => (GNATprove, Always_Return);

   function F1 (X : Integer) return Integer is
      C : T := F2'Access;
   begin
      return (if X = 1 then C (X) else 1);
   end F1;

   function F2 (X : Integer) return Integer is
      C : T := F1'Access;
   begin
      return (if X = 0 then C (X) else 0);
   end F2;
begin
   null;
end Main2;
