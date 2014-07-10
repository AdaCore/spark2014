package Simple_Sets
  with SPARK_Mode
is
   type Set is limited private;

   function Number_Of_Members (S : Set) return Natural;

   function Is_Member (S : Set; E : Integer) return Boolean;

   function Get_Member (S : Set; N : Positive) return Integer with
     Pre => N <= Number_Of_Members (S);

   procedure Add_Member (S : in out Set; E : Integer);

   procedure Destroy_Set (S : out Set) with
     Post => Number_Of_Members (S) = 0;

   function Equivalent (A, B : Set) return Boolean;

   function "=" (Left, Right : Set) return Boolean renames Equivalent;

private
   pragma SPARK_Mode (Off);

   type Set_Record;

   type Set is access Set_Record;

   type Set_Record is record
      Element : Integer;
      Next    : Set;
   end record;

end Simple_Sets;
