package body Info_Messages with SPARK_mode is
   procedure Search (A      : Nat_Array;
                     E      : Natural;
                     Found  : out Boolean;
                     Result : out Positive)
   is
   begin
      for I in A'Range loop
         if A (I) = E then
            Found := True;
            Result := I;
            return;
         end if;
      end loop;
      Found := False;
   end Search;
end Info_Messages;
