--------------------------------------------------------------------------------
-- NOM DU CSU (corps)               : InSrc.adb
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

with Ada.Text_IO;                use Ada.Text_IO;
with Ada.Exceptions;             use Ada.Exceptions;
with Ada.Characters.Handling;    use Ada.Characters.Handling;
with Ada.Strings.Maps;           use Ada.Strings.Maps;
with Ada.Characters.Latin_1;
with Ada.Strings.Maps.Constants; use Ada.Strings.Maps.Constants;

package body InSrc with
   SPARK_Mode
is

   Asciinul : constant Character := ASCII.NUL;
   Asciietx : constant Character := ASCII.ETX;
   Asciieot : constant Character := ASCII.EOT;
   Asciibel : constant Character := ASCII.BEL;
   Asciitab : constant Character := ASCII.HT;
   Asciilf  : constant Character := ASCII.LF;
   Asciiff  : constant Character := ASCII.FF;
   Asciicr  : constant Character := ASCII.CR;
   Asciinak : constant Character := ASCII.NAK;
   Asciisp  : constant Character := ' ';

   -- caractère séparateur de ligne pour le système considéré
   Newlinechar : constant Character := Asciilf;

   NormAsciiCharRange : constant Character_Range :=
     (Low => Ada.Characters.Latin_1.Space, High => Ada.Characters.Latin_1.LC_Y_Diaeresis);
   Normasciicharset : constant Character_Set := To_Set ((NormAsciiCharRange));

   Identcharset   : constant Character_Set := To_Set ('_') or Decimal_Digit_Set or Letter_Set;
   Chiffrecharset : constant Character_Set := Decimal_Digit_Set;
   Hexacharset    : constant Character_Set := Hexadecimal_Digit_Set;
   Blanccharset   : constant Character_Set :=
     (To_Set (Asciibel) or To_Set (Asciitab) or To_Set (Asciilf) or To_Set (Asciiff) or To_Set (Asciicr) or
      To_Set (Asciisp)) and
     not To_Set (Newlinechar);

   type TGenericErr is (ManqueApos, ManqueComment);

   -- Procédure donnant le nom et la ligne courante du fichier source.
   procedure Status (Object : not null access TSourceMgr; Name : out TText; Ligne : out Natural) is
   begin
      Name  := FSplitName (Object.FName);
      Ligne := Object.CptLigne;
   end Status;

   procedure FileRead (F : SrcFile.File_Type; Buffer : out Ttextbuff; Len : SrcFile.Count) is
      Ch : Character;
   begin
      for Ind in 1 .. Len loop
         SrcFile.Read (F, Ch);
         Append (Buffer, Ch);
      end loop;
   exception
      when E : others =>
         Raise_Exception
           (Exception_Identity (E), "Erreur de lecture du fichier source : """ & SrcFile.Name (F) & """.");
   end FileRead;

   -- Procédure de lecture du contenu du fichier source.
   procedure Open (Object : not null access TSourceMgr; Name : TText) is
   begin
      Object.FName    := Name;
      Object.CptCar   := 0;
      Object.CptLigne := 1;
      SrcFile.Open (Object.FRef, SrcFile.In_File, To_String (Name));
      Object.FLen := SrcFile.Size (Object.FRef);
      Put_Line ("Lecture de " & To_String (FSplitName (Name)) & " ...");
      FileRead (Object.FRef, Object.TextBuff, Object.FLen);
      SrcFile.Close (Object.FRef);
      Append (Object.TextBuff, Asciieot);
      Object.ChTemp := Element (Object.TextBuff, 1);
   exception
      when E : others =>
         Raise_Exception (Exception_Identity (E), "Erreur d'ouverture du fichier source """ & To_String (Name) & """.");
   end Open;

   -- Procédure de lecture d'un caractère du buffer contenant le texte source.
   -- Le caractère lu est dans Ch1, le suivant est dans Ch2.
   procedure Read (Object : not null access TSourceMgr; Ch1, Ch2 : out Character) is
   begin
      Ch1           := Object.ChTemp;
      Object.CptCar := Object.CptCar + 1;
      if Object.ChTemp = Newlinechar then
         Object.CptLigne := Object.CptLigne + 1;
      end if;
      if Object.ChTemp /= Asciieot then
         Object.ChTemp := Element (Object.TextBuff, Integer'Succ (Object.CptCar));
      end if;
      Ch2 := Object.ChTemp;
   end Read;

   -- Procédure de destruction du buffer.
   procedure Close (Object : not null access TSourceMgr) is
   begin
      Object.FName    := Null_Unbounded_String;
      Object.TextBuff := To_Unbounded_String ((1 => Asciieot));
   end Close;

   -- Renvoie la chaîne en minuscule.
   function LowStr (S : TText) return TText is
   begin
      return To_Unbounded_String (To_Lower (To_String (S)));
   end LowStr;

   -- Affiche la raison de l'erreur.
   procedure AffGenericErr (Id : TGenericErr) is
   begin
      Put_Line ("Erreur generique : " & TGenericErr'Image (Id));
   end AffGenericErr;

   -- Affiche une chaîne à la suite d'une erreur.
   procedure AffChaineErr (Chaine : String) is
   begin
      Put_Line (Chaine);
   end AffChaineErr;

-- Lit un ou plusieurs caractère dans le texte source et le ou les transforme en éléments lexicaux.
   procedure ReadToken (TokenId : out TTokenId; Token : out Ttokenstr) is
      Ch, ChSuivant : Character;

      -- Lit une chaîne de caractères.
      procedure ReadChaine with
         Global => (Input => SrcAuto)
      is
      begin
         Read (SrcAuto, Ch, ChSuivant);
         while Is_In (Ch, Normasciicharset) loop
            if (Ch = '`') and (ChSuivant = '`') then
               Read (SrcAuto, Ch, ChSuivant);
            end if;
            if Ch = Asciietx then
               Ch := Asciinul;
            end if;
            if (Ch = '`') and (ChSuivant /= '`') then
               Ch := Asciietx;
            end if;
            if Ch /= Asciietx then
               Token := Token & Ch;
               Read (SrcAuto, Ch, ChSuivant);
            end if;
         end loop;
         case Ch is
            when Asciieot =>
               AffGenericErr (ManqueApos);
               TokenId := ErrorId;
            when Asciietx =>
               TokenId := CarId;
            when others =>
               AffChaineErr ("" & Ch); -- !!!!
               TokenId := ErrorId;
         end case;
      end ReadChaine;

      -- Lit un commentaire.
      procedure ReadComment with
         Global => (Input => SrcAuto)
      is
         Enr : Boolean := True;
      begin
         if Ch = '(' then
            Read (SrcAuto, Ch, ChSuivant);
         end if;
         Read (SrcAuto, Ch, ChSuivant);
         while not Is_In (Ch, To_Set (Asciieot) or To_Set (Asciietx)) loop
            if Ch = Newlinechar then
               Enr := False;
            end if;
            if Ch = Asciietx then
               Ch := Asciinul;
            end if;
            if Ch = '}' then
               Ch := Asciietx;
            end if;
            if (Ch = '*') and (ChSuivant = ')') then
               Read (SrcAuto, Ch, ChSuivant);
               Ch := Asciietx;
            end if;
            if Ch /= Asciietx then
               if Enr then
                  Token := Token & Ch;
               end if;
               Read (SrcAuto, Ch, ChSuivant);
            end if;
         end loop;
         if Ch = Asciietx then
            TokenId := CommentId;
         else
            AffGenericErr (ManqueComment);
            TokenId := ErrorId;
         end if;
      end ReadComment;

      -- Lit un commentaire d'une ligne.
      procedure ReadCommentSingleLine with
         Global => (Input => SrcAuto)
      is
      begin
         if Ch = '-' then
            Read (SrcAuto, Ch, ChSuivant);
         end if;
         Read (SrcAuto, Ch, ChSuivant);
         while not Is_In (Ch, To_Set (Asciieot) or To_Set (Asciietx)) loop
            if Ch = Newlinechar then
               Ch := Asciietx;
            else
               Token := Token & Ch;
               Read (SrcAuto, Ch, ChSuivant);
            end if;
         end loop;
         if Ch = Asciietx then
            TokenId := CommentId;
         else
            AffGenericErr (ManqueComment);
            TokenId := ErrorId;
         end if;
      end ReadCommentSingleLine;

      -- Lit un identificateur.
      procedure ReadIdent with
         Global => (Input => SrcAuto)
      is
      begin
         Token := Token & Ch;
         while Is_In (ChSuivant, Identcharset) loop
            Read (SrcAuto, Ch, ChSuivant);
            Token := Token & Ch;
         end loop;
         IdAuto.Recherche (LowStr (Token), TokenId);
      end ReadIdent;

   begin
      Token   := Null_Unbounded_String;
      TokenId := ErrorId;
      Read (SrcAuto, Ch, ChSuivant);
      while Is_In (Ch, Blanccharset) loop
         Read (SrcAuto, Ch, ChSuivant);
      end loop;
      case Ch is
         when Asciieot =>
            TokenId := EotId;
         when Newlinechar =>
            TokenId := NewlineId;
         when '`' =>
            ReadChaine;
         when '(' =>
            if ChSuivant = '*' then
               ReadComment;
            else
               TokenId := ErrorId;
            end if;
         when '-' =>
            if ChSuivant = '-' then
               ReadCommentSingleLine;
            else
               TokenId := ErrorId;
            end if;
         when '+' =>
            TokenId := PlusId;
         when '.' =>
            if ChSuivant = '.' then
               TokenId := PointpointId;
               Read (SrcAuto, Ch, ChSuivant);
            else
               TokenId := UnknownId;
            end if;
         when ',' =>
            TokenId := VirgId;
         when 'A' .. 'Z' | 'a' .. 'z' | '_' =>
            ReadIdent;
         when '{' =>
            ReadComment;
         when others =>
            TokenId := UnknownId;
      end case;
   end ReadToken;

end InSrc;
