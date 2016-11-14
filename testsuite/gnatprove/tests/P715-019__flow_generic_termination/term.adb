package body Term is

   function Eq (X, Y : T) return Boolean is
   begin
      return TSet.Contains (S, X) or TSet.Contains (S, Y);
   end;

   function Hash (X : T) return Ada.Containers.Hash_Type is (0);

end;
