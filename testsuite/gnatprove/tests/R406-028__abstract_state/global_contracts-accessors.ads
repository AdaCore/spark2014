private with Global_Contracts.State;

package Global_Contracts.Accessors with SPARK_Mode is
   function Get_B1 return Boolean;
   function Get_B2 return Boolean;
   function Valid_G return Boolean is (Get_B1 and Get_B2);

   function Get_G return Integer with
     Global => S2,
     Pre    => Valid_G;
private
   function Get_B1 return Boolean is (State.B1);
   function Get_B2 return Boolean is (State.B2);
end Global_Contracts.Accessors;
