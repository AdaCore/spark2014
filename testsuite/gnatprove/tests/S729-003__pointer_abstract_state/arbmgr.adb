--------------------------------------------------------------------------------
-- NOM DU CSU (corps)               : ArbMgr.adb
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

with Ada.Unchecked_Deallocation;
package body ArbMgr with
   SPARK_Mode,
   Refined_State => (ArbMgrState => Arbre, ListeState => Liste, CurElmtState => CurElmt, OtherState => AJour)
is

   -- Définition d'un noeud pour la gestion de l'arbre binaire.
   type TNoeud;
   type PNoeud is access TNoeud;
   type TNoeud is record
      Gauche  : PNoeud;       -- branche inférieure de l'arbre
      Droit   : PNoeud;       -- branche supérieure de l'arbre
      Suivant : PNoeud;       -- liste croissante
      Clef    : TClef;        -- clef de comparaison
      Element : TElement;     -- stockage de l'élément à trier ou à rechercher
   end record;

   Arbre   : PNoeud  := null;
   CurElmt : PNoeud  := null;
   Liste   : PNoeud  := null;
   AJour   : Boolean := False;

   -- Définition du tableau pour le ré-équilibrage de l'arbre
   type TTab is array (Positive range <>) of PNoeud;
   type PTab is access TTab;

   -- Ajoute un élément à l'arbre binaire en le triant par l'ordre défini par la clef.
   procedure Ajoute (Clef : TClef; Element : TElement) with
      Refined_Global => (In_Out => Arbre)
   is
      NoeudNouveau : PNoeud;

      procedure AjouteDans (Noeud : not null PNoeud) with
         Global => (Input => NoeudNouveau)
      is
      begin
         if Clef /= Noeud.Clef then
            if Clef < Noeud.Clef then
               if Noeud.Gauche /= null then
                  AjouteDans (Noeud.Gauche);
               else
                  Noeud.Gauche := NoeudNouveau;
               end if;
            else
               if Noeud.Droit /= null then
                  AjouteDans (Noeud.Droit);
               else
                  Noeud.Droit := NoeudNouveau;
               end if;
            end if;
         end if;
      end AjouteDans;

   begin
      AJour        := False;
      NoeudNouveau := new TNoeud'(Gauche => null, Droit => null, Suivant => null, Clef => Clef, Element => Element);
      if Arbre /= null then
         AjouteDans (Arbre);
      else
         Arbre := NoeudNouveau;
      end if;
   end Ajoute;

   -- Procédure qui balance l'arbre de façon à minimiser le temps de recherche
   procedure Balance with
      Refined_Global => (In_Out => Arbre, Output => Liste)
   is
      Tab : PTab := null;

      procedure Free is new Ada.Unchecked_Deallocation (TTab, PTab);

      procedure PlaceDansTab (Noeud : not null PNoeud) with
         Global => (Input => Tab)
      is
      begin
         if Noeud.Gauche /= null then
            PlaceDansTab (Noeud.Gauche);
         end if;
         if Tab = null then
            Tab := new TTab'(Positive'First => Noeud);  -- premier élément du tableau
         else
            declare
               AncienTab : PTab := Tab;
            begin
               Tab := new TTab'(Tab (Tab'Range) & Noeud);  -- les suivants
               Free (AncienTab);
            end;
         end if;
         if Noeud.Droit /= null then
            PlaceDansTab (Noeud.Droit);
         end if;
      end PlaceDansTab;

      procedure PlaceDansArbre (Noeud : out PNoeud; Premier, Dernier : Positive) with
         Global => (Input => Tab)
      is
         Index : Positive;
      begin
         Index := (Premier + Dernier) / 2;
         Noeud := Tab (Index);
         if Premier /= Index then
            PlaceDansArbre (Noeud.Gauche, Premier, Index - 1);
         else
            Noeud.Gauche := null;
         end if;
         if Dernier /= Index then
            PlaceDansArbre (Noeud.Droit, Index + 1, Dernier);
         else
            Noeud.Droit := null;
         end if;
      end PlaceDansArbre;

      procedure PlaceDansListe (Noeud : out PNoeud) with
         Global => (Input => Tab)
      is
      begin
         Noeud := Tab (Tab'First);
         for Index in Tab'First .. Tab'Last - 1 loop
            Tab (Index).Suivant := Tab (Index + 1);
         end loop;
         Tab (Tab'Last).Suivant := null;
      end PlaceDansListe;

   begin
      if Arbre /= null then
         PlaceDansTab (Arbre);
         PlaceDansArbre (Arbre, Tab'First, Tab'Last);
         PlaceDansListe (Liste);
         Free (Tab);
         AJour := True;
      end if;
   end Balance;

   -- Procédure qui recherche un élément dans l'arbre binaire et qui renvoie son Element.
   procedure Recherche (Clef : TClef; Element : out TElement) with
      Refined_Global => (In_Out => Arbre, Output => Liste)
   is
      procedure RechercheDans (Noeud : not null PNoeud) is
      begin
         if Clef = Noeud.Clef then
            Element := Noeud.Element;
         elsif Clef < Noeud.Clef then
            if Noeud.Gauche /= null then
               RechercheDans (Noeud.Gauche);
            end if;
         elsif Noeud.Droit /= null then
            RechercheDans (Noeud.Droit);
         end if;
      end RechercheDans;

   begin
      Element := NonDefini;
      if not AJour and then AutoBal then
         Balance;
      end if;
      if Arbre /= null then
         RechercheDans (Arbre);
      end if;
   end Recherche;

   -- Fonction retournant le premier élément de la liste triée
   function RetournePremier return TElement with
      Refined_Global => (Input => (Arbre, Liste, CurElmt))
   is
   begin
      if not AJour and then AutoBal then
         Balance;
      end if;
      CurElmt := Liste;
      if CurElmt /= null then
         return CurElmt.Element;
      else
         return NonDefini;
      end if;
   end RetournePremier;

   -- Fonction retournant l'élément suivant de la liste triée
   function RetourneSuivant return TElement with
      Refined_Global => (Input => CurElmt)
   is
   begin
      if CurElmt /= null then
         CurElmt := CurElmt.Suivant;
      end if;
      if CurElmt /= null then
         return CurElmt.Element;
      else
         return NonDefini;
      end if;
   end RetourneSuivant;

   -- Procédure de destruction de l'arbre binaire.
   procedure Detruit with
      Refined_Global => (In_Out => Arbre, Output => (Liste, CurElmt))
   is

      procedure Free is new Ada.Unchecked_Deallocation (TNoeud, PNoeud);

      procedure Elimine (Noeud : not null PNoeud) is
         Dum : PNoeud := Noeud;
      begin
         if Noeud.Gauche /= null then
            Elimine (Noeud.Gauche);
         end if;
         if Noeud.Droit /= null then
            Elimine (Noeud.Droit);
         end if;
         Free (Dum);
      end Elimine;

   begin
      if Arbre /= null then
         Elimine (Arbre);
      end if;
      Arbre   := null;
      CurElmt := null;
      Liste   := null;
      AJour   := False;
   end Detruit;

end ArbMgr;
