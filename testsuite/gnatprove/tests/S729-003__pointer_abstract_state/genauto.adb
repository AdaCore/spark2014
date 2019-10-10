--------------------------------------------------------------------------------
-- NOM DU CSU (principal)           : GenAuto.adb
-- AUTEUR DU CSU                    : P. Pignard
-- VERSION DU CSU                   : 2.1a
-- DATE DE LA DERNIERE MISE A JOUR  : 18 juillet 2008
-- ROLE DU CSU                      : Programme de génération automatique d'automates.
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

with Ada.Text_IO;      use Ada.Text_IO;
with Ada.Command_Line; use Ada.Command_Line;
with BasicDef;         use BasicDef;
with InSrc;            use InSrc;
with OutSrc;           use OutSrc;
with SrcSeq;           use SrcSeq;

procedure Genauto is

   Debug : constant Boolean := False;

   procedure Ajoute (S : String; T : TTokenId) is
   begin
      IdAuto.Ajoute (To_Unbounded_String (S), T);
   end Ajoute;

   FName, UName : TText;
   FObject      : File_Type;
   Ok           : Boolean;
   Time         : Natural;

begin
   Put_Line ("Entrer les informations suivantes :");
   New_Line;
   Put ("Type des événements : ");
   Get_Line (TEventStr);
   Put ("Contexte de l'événement : ");
   Get_Line (EventDesStr);
   Put ("Type du contexte de l'événement : ");
   Get_Line (TEventDesStr);
   Put ("Constante événement nul : ");
   Get_Line (NullEventStr);
   Put ("Procédure de gestion des événements : ");
   Get_Line (GetEventStr);
   Put ("Unité(s) à inclure : ");
   Get_Line (UserUnitStr);

   --Initialisation des objets utilisés.
   DefaultInitList := new TTextListMgr;

   DefaultEventList := new TTextListMgr;

   DefaultDefaultList := new TTextListMgr;

   StateList := new TStateListMgr;

   EventList := new TEnumListMgr;

   ObjectList := new TTextListMgr;

   CallUnitList := new TEnumListMgr;

   -- Génération du 'langage' de l'automate.
   Ajoute ("action", ActionId);
   Ajoute ("automate", AutomId);
   Ajoute ("call", CallId);
   Ajoute ("default", DefaultId);
   Ajoute ("end", EndId);
   Ajoute ("error", ErrId);
   Ajoute ("event", EventId);
   Ajoute ("from", FromId);
   Ajoute ("gosub", GosubId);
   Ajoute ("init", InitId);
   Ajoute ("out", OutId);
   Ajoute ("same", SameId);
   Ajoute ("to", ToId);

   Put ("Nom du fichier source : ");
   Get_Line (FName);

   Time := Horlogems;

   SrcAuto := new TSourceMgr;
   Open (SrcAuto, FName);
   -- Exécution de l'automate.
   StartSrcSeq (Ok, Debug);
   Close (SrcAuto);

   IdAuto.Detruit;

   Put_Line ("Temps passé : " & Integer'Image (Horlogems - Time) & " milisecondes.");

   if Ok then
      FName := FSplitName (FName);
      UName := TruncLast (FName);

      -- Création de la spécification du package
      Put ("Nom de l'unité Ada (spec : " & To_String (UName) & ".ads) : ");
      Get_Line (FName);
      if FName = "" then
         FName := UName & ".ads";
      end if;

      Create (FObject, Out_File, To_String (FName));

      Put_Line (FObject, "package " & To_String (AName) & " is");
      New_Line (FObject);

      Put_Line
        (FObject,
         "procedure Start" &
         To_String (AName) &
         "(Result : out Boolean; Debug : Boolean := False);");
      New_Line (FObject);
      Put_Line (FObject, "end " & To_String (AName) & ";");

      Close (FObject);

      -- Création du corps du package
      Put ("Nom de l'unité Ada (corps : " & To_String (UName) & ".adb) : ");
      Get_Line (FName);
      if FName = "" then
         FName := UName & ".adb";
      end if;

      Create (FObject, Out_File, To_String (FName));

      if UserUnitStr /= "" then
         UserUnitStr := ", " & UserUnitStr;
      end if;
      Put (FObject, "with Ada.Text_IO" & To_String (UserUnitStr));
      TWriteToFile (CallUnitList, FObject);
      Put_Line (FObject, ";");

      Put (FObject, "use  Ada.Text_IO" & To_String (UserUnitStr));
      TWriteToFile (CallUnitList, FObject);
      Put_Line (FObject, ";");
      New_Line (FObject);

      Put_Line (FObject, "package body " & To_String (AName) & " is");
      New_Line (FObject);

      Put (FObject, "  type TState is (stError, stQuit");

      TWriteToFile (StateList, FObject);

      Put_Line (FObject, ");");
      New_Line (FObject);
      Put_Line
        (FObject,
         "procedure Automate (TheState : TState; Event : in out " &
         To_String (TEventStr) &
         "; " &
         To_String (EventDesStr) &
         " : in out " &
         To_String (TEventDesStr) &
         "; Result : out Boolean; Debug : Boolean := False) is");
      Put_Line (FObject, "  State : TState := TheState;");
      New_Line (FObject);

      WriteToFile (ObjectList, FObject);

      Put_Line (FObject, "  begin");
      Put_Line (FObject, To_String ("  Result := Event = " & NullEventStr & ";"));
      Put_Line (FObject, "  while (State /= stError) and (State /= stQuit) loop");
      Put_Line (FObject, To_String ("    while Event = " & NullEventStr & " loop"));
      Put_Line (FObject, To_String ("      " & GetEventStr & "(Event, " & EventDesStr & ");"));
      Put_Line (FObject, "    end loop;");
      Put_Line (FObject, "    if Debug then");
      Put_Line
        (FObject,
         "      Put(TState'Image(State) & ""; "" & " & To_String (TEventStr) & "'Image(Event));");
      Put_Line (FObject, "      if not Result then");
      Put_Line (FObject, "        Put(""+"");");
      Put_Line (FObject, "        Result := True;");
      Put_Line (FObject, "      end if;");
      Put_Line (FObject, "      Put_Line(""; "" & " & To_String (EventDesStr) & ");");
      Put_Line (FObject, "    end if;");
      Put_Line (FObject, "    case State is");

      AWriteToFile (StateList, FObject);

      Put_Line (FObject, "      when others =>");
      Put_Line (FObject, "        null;");
      Put_Line (FObject, "      end case;");
      Put_Line (FObject, "    end loop;");
      Put_Line (FObject, "  Result := State /= stError;");
      Put_Line (FObject, "  end Automate;");
      New_Line (FObject);
      Put_Line
        (FObject,
         "procedure Start" &
         To_String (AName) &
         "(Result : out Boolean; Debug : Boolean := False) is");
      Put_Line (FObject, "  Event : " & To_String (TEventStr) & ";");
      Put_Line (FObject, "  " & To_String (EventDesStr) & " : " & To_String (TEventDesStr) & ";");
      Put_Line (FObject, "  begin");

      Put_Line (FObject, To_String ("  " & GetEventStr & "(Event, " & EventDesStr & ");"));
      CWriteToFile (StateList, FObject);

      Put_Line (FObject, "  end Start" & To_String (AName) & ";");
      New_Line (FObject);
      Put_Line (FObject, "end " & To_String (AName) & ";");

      Close (FObject);
   else
      Set_Exit_Status (Failure);
   end if;

   Done (DefaultInitList);

   Done (DefaultEventList);

   Done (DefaultDefaultList);

   Done (ObjectList);

   Done (StateList);

   Done (EventList);

   Done (CallUnitList);

end Genauto;
