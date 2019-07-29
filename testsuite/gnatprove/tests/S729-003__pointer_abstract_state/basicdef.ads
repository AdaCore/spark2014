--------------------------------------------------------------------------------
-- NOM DU CSU (spécification)       : BasicDef.ads
-- AUTEUR DU CSU                    : P. Pignard
-- VERSION DU CSU                   : 2.2b
-- DATE DE LA DERNIERE MISE A JOUR  : 18 juillet 2008
-- ROLE DU CSU                      : Unité de définition de types et procédures.
--
--
-- FONCTIONS EXPORTEES DU CSU       :
--
--
-- FONCTIONS LOCALES DU CSU         :
--
--
-- NOTES                            :
--
--
--------------------------------------------------------------------------------

with Ada.Strings.Unbounded;

package BasicDef is

   type TText is new Ada.Strings.Unbounded.Unbounded_String;
   type PText is access TText;

   Null_Unbounded_String : constant TText := TText (Ada.Strings.Unbounded.Null_Unbounded_String);

   procedure Get_Line (Item : out TText);

   procedure Put_Line (Item : TText);

   -- Fonction qui, à partir du chemin complet d'un fichier, retourne le nom du fichier seul.
   function FSplitName (WithPath : TText) return TText;

   --Renvoie le compteur horaire interne en milisecondes.
   function Horlogems return Natural;

   -- Fonction retournant une chaîne sans le dernier élément séparé par un point
   function TruncLast (S : TText) return TText;

end BasicDef;
