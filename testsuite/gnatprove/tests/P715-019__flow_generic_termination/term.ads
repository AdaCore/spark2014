with Ada.Containers.Formal_Hashed_Sets;

package Term with Annotate => (GNATprove, Terminating) is

   type T is new Integer;

   function Eq (X, Y : T) return Boolean;
   --  This equality function is intentionally broken, because its (generated)
   --  Global contract is (Input => S). This brakes the internal routines in
   --  formal containers, which use this equality in their Pre/Post contract
   --  yet are explicitly annotated with Global => null.

   function Hash (X : T) return Ada.Containers.Hash_Type;

   package TSet is new Ada.Containers.Formal_Hashed_Sets
     (Element_Type        => T,
      Hash                => Hash,
      Equivalent_Elements => Eq);

   S : Tset.Set := TSet.Empty_Set;

end;
