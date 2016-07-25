with Ada.Strings.Hash;
with Ada.Containers.Indefinite_Hashed_Sets;
package Use_Sets is

   package Dir_Name_Sets is new Ada.Containers.Indefinite_Hashed_Sets
     (Element_Type        => String,
      Hash                => Ada.Strings.Hash,
      Equivalent_Elements => "=",
      "="                 => "=");

end Use_Sets;
