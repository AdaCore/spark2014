with Other; use Other;
pragma Elaborate_All (Other);

package body Generate_Initializes
  with Refined_State => (State => (X, Y))
is
   X, Y : Integer;

   procedure Initialize_State is
   begin
      X := 1;
      Y := 2;
   end Initialize_State;
begin
   B := G;
   C := G2;
   Initialize_State;
end Generate_Initializes;
