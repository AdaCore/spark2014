--------------------------------------------------------------------------------
-- NOM DU CSU (spécification)       : ArbMgr.ads
-- AUTEUR DU CSU                    : P. Pignard
-- VERSION DU CSU                   : 3.0a
-- DATE DE LA DERNIERE MISE A JOUR  : 27 juillet 2019
-- ROLE DU CSU                      : Unité de gestion d'un arbre binaire.
--
--
-- FONCTIONS EXPORTEES DU CSU       : Ajoute, Balance, Recherche,
--                                    RetournePremier, RetourneSuivant, Detruit
--
-- FONCTIONS LOCALES DU CSU         :
--
--
-- NOTES                            :
--
--
--------------------------------------------------------------------------------

generic

   -- Type de la clef de tri
   type TClef is private;

   -- Type des éléments triés suivant la clef
   type TElement is private;

   -- Element neutre indiquant notamment une recherche non aboutie
   NonDefini : TElement;

   -- Appel à la fonction Balance automatiquement lors d'un accès
   AutoBal : Boolean := True;

   -- Relation d'ordre de la clef de tri
   with function "<" (Left, Right : TClef) return Boolean is <>;

package ArbMgr with
   SPARK_Mode,
   Abstract_State => (ArbMgrState, ListeState, CurElmtState, OtherState)
is

   -- Procédures assurant la gestion de l'arbre binaire.
   procedure Ajoute (Clef : TClef; Element : TElement) with
      Global => (In_Out => ArbMgrState);
   procedure Balance with
      Global => (In_Out => ArbMgrState, OutPut => ListeState);
   procedure Recherche (Clef : TClef; Element : out TElement) with
      Global => (In_Out => ArbMgrState, OutPut => ListeState);
   function RetournePremier return TElement with
      Global => (Input => (ArbMgrState, ListeState, CurElmtState));
   function RetourneSuivant return TElement with
      Global => (Input => CurElmtState);
   procedure Detruit with
      Global => (In_Out => ArbMgrState, OutPut => (ListeState, CurElmtState));

end ArbMgr;
