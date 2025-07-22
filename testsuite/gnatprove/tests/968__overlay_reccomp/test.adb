procedure Test is

   type R is record
      I : Integer;
   end record;

   type RR is record
      C : R;
   end record;

   procedure Test (X : in out RR);

   procedure Test (X : in out RR) is
      Z : Integer with Import, Address => X.C'Address;
   begin
      null;
   end Test;
begin
  null;
end Test;
