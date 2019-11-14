package body sPIN.Tunnel
with
   Refined_State => (Tunnel_Internal => Internal_Var,
                     Tunnel_External => External_Var)
is

   Internal_Var : Integer := 0;

   External_Var : Integer
   with
      Volatile,
      Async_Writers,
      Import;

   ----------------------------------------------------------------------------

   procedure Became_Valid
      (Result : out Boolean)
   is
      Old : constant Integer := External_Var;
   begin
      Result := Internal_Var < Old;
      Internal_Var := Old;
   end Became_Valid;

   ----------------------------------------------------------------------------

   procedure Still_Valid
      (Result : out Boolean)
   is
      Old : constant Integer := External_Var;
   begin
      Result := Internal_Var = Old;
   end Still_Valid;

   ----------------------------------------------------------------------------

   function Is_Valid return Boolean
   is (Internal_Var mod 2 = 1);

end sPIN.Tunnel;
