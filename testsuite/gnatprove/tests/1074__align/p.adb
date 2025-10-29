procedure P with SPARK_Mode is

   type R is record
      F : Integer;
      G : aliased Integer;
   end record;

   X : R;
   XF : Integer with Import, Address => X.F'Address;
   XG : Integer with Import, Address => X.G'Address;

begin
   null;
end P;
