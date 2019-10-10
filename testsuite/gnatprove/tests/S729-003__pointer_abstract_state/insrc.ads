--------------------------------------------------------------------------------
-- NOM DU CSU (spécification)       : InSrc.ads
-- AUTEUR DU CSU                    : P. Pignard
-- VERSION DU CSU                   : 3.0a
-- DATE DE LA DERNIERE MISE A JOUR  : 27 juillet 2019
-- ROLE DU CSU                      : Unité de gestion des textes sources.
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

with Ada.Direct_IO;
with ArbMgr;
with BasicDef; use BasicDef;

package InSrc with
   SPARK_Mode
is

   -- Objet assurant la gestion du fichier source.
   type TSourceMgr is tagged limited private;
   type PSourceMgr is access TSourceMgr;

   procedure Open (Object : not null access TSourceMgr; Name : TText);
   procedure Read (Object : not null access TSourceMgr; Ch1, Ch2 : out Character);
   procedure Status (Object : not null access TSourceMgr; Name : out TText; Ligne : out Natural);
   procedure Close (Object : not null access TSourceMgr);

   -- Eléments lexicaux
   type TTokenId is
     (NullId, EotId, NewlineId, ErrorId, UnknownId, CallId, CarId, CommentId, UndefId, AutomId, DefaultId, OutId, ErrId,
      FromId, InitId, EventId, ActionId, VirgId, PlusId, PointpointId, ToId, GosubId, EndId, SameId);

   -- Contexte de l'élément lexical
   subtype Ttokenstr is TText;

   -- Lit un ou plusieurs caractères dans le texte source et le ou les transforme en éléments lexicaux.
   procedure ReadToken (TokenId : out TTokenId; Token : out Ttokenstr);

   -- Référence du package assurant la gestion des mots clés
   package IdAuto is new ArbMgr (TText, TTokenId, UndefId);

   SrcAuto : PSourceMgr;     -- Référence de l'objet assurant la gestion du texte source de l'automate

private

   package SrcFile is new Ada.Direct_IO (Character);

   subtype Ttextbuff is TText;

   -- Objet assurant la gestion du fichier source.
   type TSourceMgr is tagged limited record
      FName            : TText;
      FRef             : SrcFile.File_Type;
      FLen             : SrcFile.Count;
      CptCar, CptLigne : Natural;
      TextBuff         : Ttextbuff;
      ChTemp           : Character;
   end record;

end InSrc;
