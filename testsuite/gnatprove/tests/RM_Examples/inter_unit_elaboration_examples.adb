with Inter_2;
pragma Elaborate_All (Inter_2);  --  Ensure body of called function G has
                                 --  been elaborated.

package body Inter_Unit_Elaboration_Examples is
   procedure P (I : in out Integer) is
   begin
      I := 2 * I;
   end P;
begin
   Y := Inter_2.G (20);  --  Call to G is ok because the body of
                         --  G is sure to have been elaborated.
end Inter_Unit_Elaboration_Examples;
