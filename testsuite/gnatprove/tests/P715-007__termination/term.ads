with Ext; pragma Elaborate_All (Ext);
package Term with SPARK_Mode is
   function Loop_Except_On_Zero (X : Natural) return Natural with
     Post => (if X = 0 then Loop_Except_On_Zero'Result = 0 else False);

   procedure Do_Not_Loop (X : in out Natural) with
     Post => False;  --@POSTCONDITION:FAIL

   C : constant Integer := Ext.C;

   subtype Empty_If_C_Is_Neg is Integer range 0 .. C;

   function Loop_If_C_Is_Neg return Empty_If_C_Is_Neg;

   procedure Still_Do_Not_Loop with
     Post => C >= 0;  --@POSTCONDITION:FAIL
end Term;
