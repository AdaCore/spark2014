procedure P is
   type T is array (1 .. 2) of Boolean;
   X : T;

   type R is record
      B : Boolean;
   end record;

   Y : R;


   procedure Assign (B : in out Boolean) is
   begin
      B := True;
   end Assign;
begin
   Assign (X (1));
   Assign (Y.B);
end P;

