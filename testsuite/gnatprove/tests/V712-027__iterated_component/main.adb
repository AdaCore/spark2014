procedure Main is
   type T is array (Integer range 1 .. 5) of Natural;
   function Ones return T is
   begin
      return (others => 1);
   end;
   X : T := (for J of Ones => J + 1);
begin
   null;
end;
