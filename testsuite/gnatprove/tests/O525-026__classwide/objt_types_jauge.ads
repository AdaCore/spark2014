-- Ada

with SPARK.Containers.Formal.Unbounded_Vectors;

-- Jauge

with Objt_Interface_Jauge;

package Objt_Types_Jauge is


   --Pour les listes d'objets jauges.

   Nb_Maximum_Jauge : Constant Positive := 4;

   subtype tIndex_Liste_Jauge is Positive range Positive'First..Nb_Maximum_Jauge;

   use Objt_Interface_Jauge;

   package Objt_Liste_Jauge is new SPARK.Containers.Formal.Unbounded_Vectors(Index_Type                   => tIndex_Liste_Jauge,

                                                                            Element_Type                 => tInterface_Jauge'Class

									        );

end Objt_Types_Jauge;
