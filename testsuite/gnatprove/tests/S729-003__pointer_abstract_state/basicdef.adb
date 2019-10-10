--------------------------------------------------------------------------------
-- NOM DU CSU (corps)               : BasicDef.adb
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

with Ada.Calendar;             use Ada.Calendar;
with Ada.Text_IO;              use Ada.Text_IO;
with Ada.Directories;          use Ada.Directories;
with Ada.Text_IO.Unbounded_IO; use Ada.Text_IO.Unbounded_IO;

package body BasicDef is

   -- Fonction qui, à partir du chemin complet d'un fichier, retourne le nom du fichier seul.
   function FSplitName (WithPath : TText) return TText is
   begin
      return To_Unbounded_String (Simple_Name (To_String (WithPath)));
   end FSplitName;

   --Renvoie le compteur horaire interne en milisecondes.
   function Horlogems return Natural is
   begin
      return Natural (Seconds (Clock) * 1000.0);
   end Horlogems;

   procedure Get_Line (Item : out TText) is
   begin
      Get_Line (Ada.Strings.Unbounded.Unbounded_String (Item));
   end Get_Line;

   procedure Put_Line (Item : TText) is
   begin
      Put_Line (Ada.Strings.Unbounded.Unbounded_String (Item));
   end Put_Line;

   -- Fonction retournant une chaîne sans le dernier élément séparé par un point
   function TruncLast (S : TText) return TText is
   begin
      return Head (S, Index (S, ".", Ada.Strings.Backward) - 1);
   end TruncLast;

end BasicDef;
