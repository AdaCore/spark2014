procedure Conv with SPARK_Mode is
   subtype T is Integer range 1 .. 10;
   subtype T2 is Integer range 1 .. 10;
   type Ptr is access T;
   X : Ptr;
   Y : access T2 := X;

   function F (Y : access T2) return Boolean with
     Import;

   B : Boolean := F (X);

   procedure P (Y : access T2 := X) with
     Import;

   function G (X : Ptr) return access T2 is (X);

   function H (X : Ptr) return access T2 is
   begin
      return R : access T := X do
         return;
      end return;
   end H;

   function I (X : Ptr) return access T2 is
   begin
      return X;
   end I;

   package Nested is
      type Root is tagged record
         F : Integer;
      end record;
      function J (X : access Root) return Boolean with
        Import;
      type Child is new Root with null record;
      type Child_Ptr is access Child;
   end Nested;
   use Nested;

   C : Child_Ptr := new Child'(F => 0);
   Z : access Child := C;

   A : Boolean := J (Z);  --  The type of the formal of the inherited function
                          --  J on Child is access Root, so both types are
                          --  incompatible.
begin
   P;
end;
