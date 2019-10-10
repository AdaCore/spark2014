with Ada.Real_Time;

package P with Initializes => null is
   X : Boolean;

   function Truth return Boolean is (True) with Pre => X, Global => (Proof_In => X);

   procedure Dummy with Global => (Input => Ada.Real_Time.Clock_Time);
   --  This Global contract should include Proof_In => X

end;
