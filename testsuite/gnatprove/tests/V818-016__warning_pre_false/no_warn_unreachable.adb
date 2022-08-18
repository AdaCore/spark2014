procedure No_Warn_Unreachable (X : Integer)
with
  SPARK_Mode,
  Global => null,
  Pre => X > 0
is

   function Unreachable return Boolean is (True)
     with Pre => False;

   subtype Negative is Integer range Integer'First .. -1;

   B : Boolean :=
     (if X > 0 then True
      else Unreachable);
begin
   B :=
     (case X is
        when 1 => True,
        when 42 => False,
        when 0 => Unreachable,
        when Negative => Unreachable,
        when others => True);

end;
