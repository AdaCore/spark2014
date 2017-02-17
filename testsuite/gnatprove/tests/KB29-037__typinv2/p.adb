package body P is
   procedure Bad (V : in out T) is
   begin
      V.Access_Count := V.Access_Count + 1;
      V.Locked := True;
   end Bad;
end P;
