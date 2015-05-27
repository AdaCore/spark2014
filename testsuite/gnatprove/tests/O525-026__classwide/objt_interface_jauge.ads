

package Objt_Interface_Jauge is

   type tInterface_Jauge is interface;

 function Is_Niveau_Bas (Jauge : tInterface_Jauge'Class) return Boolean is abstract;

end Objt_Interface_Jauge;
