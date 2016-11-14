with Ada.Containers.Formal_Hashed_Sets;

package Term is

   type T is new Integer;

   function Eq (X, Y : T) return Boolean;

   function Hash (X : T) return Ada.Containers.Hash_Type;

   package TSet is new Ada.Containers.Formal_Hashed_Sets
     (Element_Type        => T,
      Hash                => Hash,
      Equivalent_Elements => Eq,
      "="                 => "=");

   S : Tset.Set := TSet.Empty_Set;

end;
