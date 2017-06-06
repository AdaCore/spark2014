with Sc_Status_Type;
use type Sc_Status_Type.Object_Type;

package Achiever with SPARK_Mode is

   type Internal_State is new Integer;

   procedure Do_Stuff (St :in Integer) with
     Post =>
       Eq (Get_Internal_State'Old, 0);

   function Get_Internal_State return Internal_State is (0);
   function Eq (X, Y : Internal_State) return Boolean is (X = Y);

end Achiever;
