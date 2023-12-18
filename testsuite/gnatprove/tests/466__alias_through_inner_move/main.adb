with Ada.Unchecked_Deallocation;
procedure Main with SPARK_Mode is
   type A is access Integer;
   procedure Free is new Ada.Unchecked_Deallocation (Integer, A);
   type R is record
      Held : A;
   end record;
   X : A := new Integer'(0);
   Y : A :=
     R'(Held => (declare I : constant Integer := 0; begin X)).Held;
begin
   X.all := 1;
   Free (X);
   pragma Assert (Y.all = 0);
   Free (Y);
end Main;
