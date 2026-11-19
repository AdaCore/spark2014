package P is
   type T is tagged record
      Value : Integer := 0;
   end record;

   type R is record
      C : T;
   end record;

   X : constant R := (others => <>);
end P;
