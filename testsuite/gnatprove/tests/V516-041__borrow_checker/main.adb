procedure Main with SPARK_Mode is
   package Nested is
      type T1 is tagged private with
        Default_Initial_Condition,
        Annotate => (GNATprove, Ownership);
   private
      pragma SPARK_Mode (Off);
      type T1 is tagged null record;
   end Nested;
   use Nested;

   type C_Acc is access constant Integer;

   package Nested_2 is
      type T2 is new T1 with record
         F : aliased Integer := 0;
         G : C_Acc;
      end record;

   end Nested_2;
   use Nested_2;

   type Int_Acc is access all Integer;

   function Rand (X : Integer) return Boolean with
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return);

   function Read (X : T2) return Boolean with
     Import,
     Global => null,
     Annotate => (GNATprove, Always_Return);

   X : T2;
   Y : T2;
   C : Int_Acc;

begin
   if Rand (0) then
      C := X.F'Access;
      pragma Assert (Read (X)); --  Error, X.F was moved
   else
      X.G := new Integer'(14);
      Y := X;
      pragma Assert (Read (X)); --  Error, X.<hidden> was moved
   end if;
end Main;
