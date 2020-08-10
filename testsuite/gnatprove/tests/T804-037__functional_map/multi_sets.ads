with Ada.Containers.Functional_Maps;

package Multi_Sets is

   package Occ_Map is new Ada.Containers.Functional_Maps
        (Key_Type     => Integer,
         Element_Type => Positive);

end Multi_Sets;
