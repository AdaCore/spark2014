private with Global_Contracts.State;

package Global_Contracts.Accessors with SPARK_Mode is
   function Get_B1 return Boolean;

   function Get_G return Integer with
     Global => (Input => S2, Proof_In => S1),
     Pre    => Get_B1;

private
   function Get_B1 return Boolean is (State.B1);

   --  Dummy code just to trigger VC generation
   function Zero return Integer is (0);
   pragma Assert (Zero = Zero);

end Global_Contracts.Accessors;
