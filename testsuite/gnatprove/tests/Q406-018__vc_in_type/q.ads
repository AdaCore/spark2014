package Q is

   type A is array (Boolean) of Integer;

   type T is record
      C : A := (others => 0);  --  no VC here
   end record;

end;
