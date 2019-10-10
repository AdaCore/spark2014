--------------------------------------------------------------------------------
-- NOM DU CSU (spécification)       : OutSrc.ads
-- AUTEUR DU CSU                    : P. Pignard
-- VERSION DU CSU                   : 3.0a
-- DATE DE LA DERNIERE MISE A JOUR  : 27 juillet 2019
-- ROLE DU CSU                      : Unité de gestion du package résultat.
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

with Ada.Text_IO; use Ada.Text_IO;
with BasicDef;    use BasicDef;

package OutSrc with
   SPARK_Mode
is

   -- Objet assurant l'écriture du package Ada
   type TTextListMgr is tagged private;
   type PTextListMgr is access TTextListMgr;

   procedure Add (Object : not null access TTextListMgr; S : TText);
   procedure Add (Object : not null access TTextListMgr; S : String);
   procedure AddNew (Object : not null access TTextListMgr; S : TText);
   procedure AddNew (Object : not null access TTextListMgr; S : String);
   procedure WriteToFile (Object : not null access TTextListMgr; F : File_Type);
   procedure CopyTo (Object : not null access TTextListMgr; DstText : not null access TTextListMgr);
   procedure Done (Object : not null access TTextListMgr);

   -- Objet assurant l'écriture d'énumérés
   type TEnumListMgr is new TTextListMgr with private;
   type PEnumListMgr is access TEnumListMgr;

   -- Ajoute un élément s'il ne l'a pas déjà été
   procedure AddUniq (Object : not null access TEnumListMgr; S : TText);
   -- Ecrit le type des énumérés dans le fichier F
   procedure TWriteToFile (Object : not null access TEnumListMgr; F : File_Type);

   -- Objet assurant l'écriture des états de l'automate
   type TStateListMgr is new TEnumListMgr with private;
   type PStateListMgr is access TStateListMgr;

   -- Ecrit le corps des états dans le fichier F
   procedure AWriteToFile (Object : not null access TStateListMgr; F : File_Type);
   -- Ecrit l'appel du premier état dans le fichier F
   procedure CWriteToFile (Object : not null access TStateListMgr; F : File_Type);

   -- Variables utilisées dans l'automate :

   -- Référence de l'objet assurant la gestion du texte de l'initialisation
   DefaultInitList : PTextListMgr;

   -- Référence de l'objet assurant la gestion du texte des événements
   DefaultEventList : PTextListMgr;

   -- Référence de l'objet assurant la gestion du texte par défaut
   DefaultDefaultList : PTextListMgr;

   -- Référence de l'objet assurant la gestion du nom des états
   StateList : PStateListMgr;

   -- Référence de l'objet assurant la gestion du nom des des évènements
   EventList : PEnumListMgr;

   -- Référence de l'objet assurant la gestion du texte objet de l'unité Pascal
   ObjectList : PTextListMgr;

   -- Référence d'un objet texte
   DefaultOutputList : PTextListMgr;

   -- Référence de l'objet assurant la gestion du nom des unités
   CallUnitList : PEnumListMgr;

   FlLocalDefault, FlDefaultDefault, FlGosub : Boolean;

   TEventStr, EventDesStr, TEventDesStr, NullEventStr, StateToStr, GetEventStr, UserUnitStr : TText;

   AName     : TText;
   NomFich   : TText;
   LigneFich : Natural;

private

   type TTextList;
   type PTextList is access TTextList;
   -- Ligne de texte du package Ada
   type TTextList is record
      Next : PTextList;
      Text : TText;
   end record;

   -- Objet assurant l'écriture du package Ada
   type TTextListMgr is tagged record
      FirstElt, CurElt : PTextList := null;
      CurStr           : TText     := Null_Unbounded_String;
   end record;

   -- Objet assurant l'écriture d'énumérés
   type TEnumListMgr is new TTextListMgr with null record;

   -- Objet assurant l'écriture des états de l'automate
   type TStateListMgr is new TEnumListMgr with null record;

end OutSrc;
