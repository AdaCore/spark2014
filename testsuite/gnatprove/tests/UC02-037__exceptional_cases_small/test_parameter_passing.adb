procedure Test_Parameter_Passing with SPARK_Mode is

   E : exception;

   procedure P (X : in out Integer) with
     Import,
     Global => null,
     Exceptional_Cases => (E => True);

   procedure Test_By_Copy (X : aliased out Integer) with
     Exceptional_Cases => (E => X = 0);

   procedure Test_By_Copy (X : aliased out Integer) is
   begin
      X := 0;
      P (X);
   end Test_By_Copy;

   package Nested is
      type Root is tagged record
         F : Integer;
      end record;
   end Nested;
   use Nested;

   procedure P (X : aliased out Integer; Y : out Root; Z : not null access Integer) with
     Import,
     Global => null,
     Exceptional_Cases => (E => X = 1 and Y.F = 1 and Z.all = 1);

   procedure Test_By_Reference (X : aliased out Integer; Y : out Root; Z : not null access Integer) with
     Exceptional_Cases => (E => X = 1 and then Y.F = 1 and then Z.all = 1);

   procedure Test_By_Reference (X : aliased out Integer; Y : out Root; Z : not null access Integer) is
   begin
      P (X, Y, Z);
   end Test_By_Reference;

   type R is record
      F : Integer;
   end record;

   procedure P (X : in out R) with
     Import,
     Global => null,
     Exceptional_Cases => (E => True);

   procedure Test_Unknown (X : aliased out R) with
     Exceptional_Cases => (E => X.F = 0);  --  should not be provable

   procedure Test_Unknown (X : aliased out R) is
   begin
      X.F := 0;
      P (X);
   end Test_Unknown;

begin
   null;
end;
