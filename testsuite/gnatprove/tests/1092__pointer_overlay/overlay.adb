procedure Overlay is

   type Int_Access is access constant Integer;

   procedure P (X : not null Int_Access) is
      C : constant Integer with Address => X.all'Address, Import;
   begin
      null;
   end P;

   type R is record
     A : Int_Access;
     B : Integer;
   end record;

   procedure P (X : R) is
      C : constant Integer with Address => X.A.all'Address, Import;
   begin
      null;
   end P;
begin
  null;
end Overlay;
