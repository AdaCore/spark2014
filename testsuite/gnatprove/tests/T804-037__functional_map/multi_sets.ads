with SPARK.Containers.Functional.Maps;

package Multi_Sets is

   package Occ_Map is new SPARK.Containers.Functional.Maps
        (Key_Type     => Integer,
         Element_Type => Positive);

end Multi_Sets;
