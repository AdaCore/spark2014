with System;
procedure Main with SPARK_Mode is

   subtype Even is Natural
   with Dynamic_Predicate => Even mod 2 = 0;

    procedure Nat_1 (X : Natural) with Pre => X mod 2 = 0;
    procedure Nat_2 (X : Natural; D : System.Address);

    procedure Nat_1 (X : Natural) is null;
    procedure Nat_2 (X : Natural; D : System.Address) is
       Y : Even with Import, Address => D;
    begin
       Nat_1 (Y);
       Nat_1 (X);
    end Nat_2;


begin
   null;
end Main;
