package P is

   type T is array (Boolean) of Boolean;

   X : constant T := (others => False);
   --  do we need a length check here?

end;
