procedure Infeasible_Access_Subp with SPARK_Mode is
   type Bad is not null access function (I : Integer) return Integer with Post => False; --@FEASIBLE_POST:FAIL

   function F (X : Bad; I : Integer) return Integer with
     Annotate => (GNATprove, Always_Return),
     Post => False;

   function F (X : Bad; I : Integer) return Integer is
      C : constant Integer := X.all (I);
   begin
      return C;
   end F;

   function G1 (I : Integer) return Integer with Post => False;

   function G2 (I : Integer) return Integer with Post => False;

   function G1 (I : Integer) return Integer is
      G2A : constant Bad   := (if I = 0 then G2'Access else null);
      C : constant Integer := (if I = 0 then F (G2'Access, I) else I);
   begin
      return C;
   end G1;

   function G2 (I : Integer) return Integer is
      G1A : constant Bad   := (if I = 1 then G1'Access else null);
      C : constant Integer := (if I = 1 then F (G1'Access, I) else I);
   begin
      return C;
   end G2;
begin
   null;
end;
