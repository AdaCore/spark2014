function Identity (X : Boolean) return Boolean with
   Post => Identity'Result = X
is
begin
   return Y : constant Boolean := X do
      case X is
         when True =>
            null;
         when others =>
            return;
      end case;
   end return;
end Identity;
