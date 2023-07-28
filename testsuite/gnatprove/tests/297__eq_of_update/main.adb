procedure Main with SPARK_Mode is

   --  Test special handling for equal of update in the term domain

   type Int_Array is array (Positive range <>) of Integer;

   function Is_True (X : Boolean) return Boolean is (X = True);
   --  Function to ensure that the equality is translated in the term domain

   procedure Set (A : in out Int_Array; P : Positive; V : Integer) with
     Pre  => P in A'Range,
     Post => Is_True (A = (A'Old with delta P => V));

   procedure Set (A : in out Int_Array; P : Positive; V : Integer) is
   begin
      A (P) := V;
   end Set;

   A : Int_Array := (1 .. 10 => 1);
begin
   Set (A, 5, 2);
   pragma Assert (A = (5 => 2, 1 .. 4 | 6 .. 10 => 1));
end Main;
