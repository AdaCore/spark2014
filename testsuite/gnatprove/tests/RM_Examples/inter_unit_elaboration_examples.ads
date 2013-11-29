with Inter_1;
pragma Elaborate_All (Inter_1);  --  Ensure the body of the called function F
                                 --  has been elaborated.

package Inter_Unit_Elaboration_Examples is
   X : Integer := Inter_1.F (10);  --  The call to F is ok because its body is
                                   --  sure to have been elaborated.
   Y : Integer;

   procedure P (I : in out Integer);  --  P is declared so that the package
                                      --  requires a body for this example.
end Inter_Unit_Elaboration_Examples;
