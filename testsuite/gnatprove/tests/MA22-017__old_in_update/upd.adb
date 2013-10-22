procedure Upd is
   type Arr is array (Boolean) of Boolean;
   procedure Toggle (A : in out Arr; B : Boolean) with
     Post => A = A'Update (B => not A'Old(B))
   is
   begin
      A (B) := not A (B);
   end Toggle;
   A : Arr := (True, False);
begin
   Toggle (A, True);
   Toggle (A, False);
end Upd;
