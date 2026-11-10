with Ada.Containers.Indefinite_Holders;

package P is
   package H is new Ada.Containers.Indefinite_Holders (Integer);
   type R is record
      C : H.Holder;
   end record;
   X : constant R := (others => <>);
end P;
