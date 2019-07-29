--------------------------------------------------------------------------------
-- NOM DU CSU (corps)               : OutSrc.adb
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

with Ada.Unchecked_Deallocation;
package body OutSrc with
   SPARK_Mode
is

   -- Ajout d'une chaîne sans changer de ligne.
   procedure Add (Object : not null access TTextListMgr; S : TText) is
   begin
      Object.CurStr := Object.CurStr & S;
   end Add;

   -- Ajout d'une chaîne avec changement de ligne.
   procedure AddNew (Object : not null access TTextListMgr; S : TText) is
   begin
      if Object.FirstElt = null then
         Object.FirstElt := new TTextList;
         Object.CurElt   := Object.FirstElt;
      else
         Object.CurElt.Next := new TTextList;
         Object.CurElt      := Object.CurElt.Next;
      end if;
      Object.CurStr      := Object.CurStr & S;
      Object.CurElt.Text := Object.CurStr;
      Object.CurElt.Next := null;
      Object.CurStr      := Null_Unbounded_String;
   end AddNew;

   -- Ajout d'une chaîne sans changer de ligne.
   procedure Add (Object : not null access TTextListMgr; S : String) is
   begin
      Object.CurStr := Object.CurStr & S;
   end Add;

   -- Ajout d'une chaîne avec changement de ligne.
   procedure AddNew (Object : not null access TTextListMgr; S : String) is
   begin
      AddNew (Object, To_Unbounded_String (S));
   end AddNew;

   -- Ecriture du texte dans un fichier.
   procedure WriteToFile (Object : not null access TTextListMgr; F : File_Type) is
      P : PTextList := Object.FirstElt;
   begin
      while P /= null loop
         Put_Line (F, To_String (P.Text));
         P := P.Next;
      end loop;
   end WriteToFile;

   -- Transfert le texte dans un autre objet.
   procedure CopyTo (Object : not null access TTextListMgr; DstText : not null access TTextListMgr) is
      Dum : PTextList := Object.FirstElt;
   begin
      while Dum /= null loop
         if Dum.Text /= "" then
            AddNew (DstText, Dum.Text);
         end if;
         Dum := Dum.Next;
      end loop;
      Add (DstText, Object.CurStr);
   end CopyTo;

   -- Procédure de destruction du texte.
   procedure Done (Object : not null access TTextListMgr) is

      procedure Free is new Ada.Unchecked_Deallocation (TTextList, PTextList);

      Dum  : PTextList := Object.FirstElt;
      Dum2 : PTextList;

   begin
      while Dum /= null loop
         if Dum.Text /= "" then
            Dum.Text := Null_Unbounded_String;
         end if;
         Dum2 := Dum;
         Free (Dum2);
         Dum := Dum.Next;
      end loop;
      Object.FirstElt := null;
      Object.CurElt   := null;
      Object.CurStr   := Null_Unbounded_String;
   end Done;

   -- Ajoute un élément s'il ne l'a pas déjà été
   procedure AddUniq (Object : not null access TEnumListMgr; S : TText) is
      P     : PTextList := Object.FirstElt;
      Found : Boolean   := False;
   begin
      while (P /= null) and not Found loop
         if S = P.Text then
            Found := True;
         end if;
         P := P.Next;
      end loop;
      if not Found then
         AddNew (Object, S);
      end if;
   end AddUniq;

   -- Ecrit la liste sous forme d'un type énuméré
   procedure TWriteToFile (Object : not null access TEnumListMgr; F : File_Type) is
      Cpt : Integer   := 0;
      P   : PTextList := Object.FirstElt;
   begin
      while P /= null loop
         Cpt := (Cpt + 1) mod 10;
         Put (F, ", " & To_String (P.Text));
         if Cpt = 0 then
            New_Line (F);
         end if;
         P := P.Next;
      end loop;
   end TWriteToFile;

   -- Ecrit la liste sous forme d'un appel de procédure
   procedure AWriteToFile (Object : not null access TStateListMgr; F : File_Type) is
      P : PTextList := Object.FirstElt;
   begin
      while P /= null loop
         Put_Line (F, "      when " & To_String (P.Text) & " => Action" & To_String (P.Text) & ";");
         P := P.Next;
      end loop;
   end AWriteToFile;

   -- Ecrit la liste sous forme d'un appel à la procedure de départ de l'automate
   procedure CWriteToFile (Object : not null access TStateListMgr; F : File_Type) is
   begin
      if Object.FirstElt /= null then
         Put_Line
           (F,
            "  Automate(" & To_String (Object.FirstElt.Text) & ", Event, " & To_String (EventDesStr) &
            ", Result, Debug);");
      end if;
   end CWriteToFile;

end OutSrc;
