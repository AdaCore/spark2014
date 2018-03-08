package Priv is
   type T is private;


private
   type T is record
      A : Integer;
   end record;

   Ob : T := (others => <>);
end Priv;
