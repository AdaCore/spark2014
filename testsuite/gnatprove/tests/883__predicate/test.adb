with Ext; use Ext;
procedure Test with SPARK_Mode is
   subtype S is T with Predicate => P (S);

   procedure Test (X : S) is
   begin
      pragma Assert (P (X)); --  Unprovable for now
   end Test;

   procedure Test_2 (X : T; O : out S) is
   begin
      O := X; --  @PREDICATE_CHECK:FAIL
   end Test_2;

begin
   null;
end;
