procedure Main is

   --  A global variable with a setter & getter routines and
   --  dummy preconditions to prevent inlining-for-proof.

   X : Boolean;

   procedure Set with Pre => True is
   begin
      X := True;
   end;

   function Get return Boolean is (X) with Pre => True;

   --  The same routine with the same explicit and generated globals;
   --  both wrongly claim X to be an In_Out global (because GG is unaware
   --  of the Set->Get order).

   procedure Explicit with Global => (In_Out => X) is
   begin
      Set;
      pragma Assert (Get);
   end;

   procedure Implicit is
   begin
      Set;
      pragma Assert (Get);
   end;

begin
   null;
end;
