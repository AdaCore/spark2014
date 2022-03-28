procedure Aggr is

   type T is record
      X : Integer;
      Y : Integer := 0;
   end record
     with Relaxed_Initialization;

   War : T := (others => <>);

   type Arr is array (1 .. 10) of T;
   Gar : Arr := (others => <>);

   type U is record
      Y : Integer;
      Z : T;
   end record;

   Var : U := (Y => 0, Z => <>);
begin
   pragma Assert (Var.Y = 0);
end Aggr;
