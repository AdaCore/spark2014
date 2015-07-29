package body Generate_Initializes2
  with Refined_State => (State => (Priv, Hidden))
is
   Hidden : Integer;

   procedure Initialize_State is
   begin
      Priv   := Get_Private;
      Hidden := Get_Hidden;
   end Initialize_State;

begin
   Initialize_State;  --  Problem with Other.Hidden_Var
end Generate_Initializes2;
