with Ada.Text_IO, InSrc, OutSrc, BasicDef;
use  Ada.Text_IO, InSrc, OutSrc, BasicDef;

package body SrcSeq is

  type TState is (stError, stQuit, DA1, DA2, DA3, DA5, ET1, ET2, ET3, ET4, EV1, EV2
, EV3, EV4, EV5, EV6, A1, A2, A3, A4, D1, D2
, D3, D4, D5, Fin);

procedure Automate (TheState : TState; Event : in out TTokenId; Token : in out TTokenStr; Result : out Boolean; Debug : Boolean := False) is
  State : TState := TheState;

procedure ActionDA1 is
  DumEvent : TTokenId;

  begin
  DumEvent := NullId;
  flLocalDefault := False; flDefaultDefault := False; flGosub:=False;
  case Event is
    when CommentId =>
      null;
    when NewLineId =>
      if Debug then
        Status(SrcAuto, NomFich, LigneFich);
        Put_Line("Fichier " & NomFich & ", ligne " & Integer'Image(LigneFich));
      end if;
      null;
    when AutomId =>
      State := DA2;
    when others =>
      Status(SrcAuto, NomFich, LigneFich);
      Put_Line("Erreur de syntaxe à la ligne " & Integer'Image(LigneFich) & " , " & TTokenId'Image(Event) & " , " & Token);
      State := stError;
    end case;
  Event := DumEvent;
  end;


procedure ActionDA2 is
  DumEvent : TTokenId;

  begin
  DumEvent := NullId;
  case Event is
    when CommentId =>
      null;
    when NewLineId =>
      if Debug then
        Status(SrcAuto, NomFich, LigneFich);
        Put_Line("Fichier " & NomFich & ", ligne " & Integer'Image(LigneFich));
      end if;
      null;
    when UndefId =>
      AName := Token;
      State := DA3;
    when others =>
      Status(SrcAuto, NomFich, LigneFich);
      Put_Line("Erreur de syntaxe à la ligne " & Integer'Image(LigneFich) & " , " & TTokenId'Image(Event) & " , " & Token);
      State := stError;
    end case;
  Event := DumEvent;
  end;


procedure ActionDA3 is
  DumEvent : TTokenId;

  begin
  DumEvent := NullId;
  case Event is
    when CommentId =>
      null;
    when NewLineId =>
      if Debug then
        Status(SrcAuto, NomFich, LigneFich);
        Put_Line("Fichier " & NomFich & ", ligne " & Integer'Image(LigneFich));
      end if;
      null;
    when FromId =>
      declare
        LResult : Boolean;
      begin
        Automate(ET1, DumEvent, Token, LResult, Debug);
        if LResult then
      State := DA5;
            else
          State := stError;
          end if;
        end;
    when DefaultId =>
      declare
        LResult : Boolean;
      begin
        Automate(D1, DumEvent, Token, LResult, Debug);
        if LResult then
      State := DA5;
            else
          State := stError;
          end if;
        end;
    when others =>
      Status(SrcAuto, NomFich, LigneFich);
      Put_Line("Erreur de syntaxe à la ligne " & Integer'Image(LigneFich) & " , " & TTokenId'Image(Event) & " , " & Token);
      State := stError;
    end case;
  Event := DumEvent;
  end;


procedure ActionDA5 is
  DumEvent : TTokenId;

  begin
  DumEvent := NullId;
  case Event is
    when CommentId =>
      null;
    when NewLineId =>
      if Debug then
        Status(SrcAuto, NomFich, LigneFich);
        Put_Line("Fichier " & NomFich & ", ligne " & Integer'Image(LigneFich));
      end if;
      null;
    when FromId =>
      declare
        LResult : Boolean;
      begin
        Automate(ET1, DumEvent, Token, LResult, Debug);
        if LResult then
      State := DA5;
            else
          State := stError;
          end if;
        end;
    when EndId =>
      State := fin;
    when others =>
      Status(SrcAuto, NomFich, LigneFich);
      Put_Line("Erreur de syntaxe à la ligne " & Integer'Image(LigneFich) & " , " & TTokenId'Image(Event) & " , " & Token);
      State := stError;
    end case;
  Event := DumEvent;
  end;


procedure ActionET1 is
  DumEvent : TTokenId;

  begin
  DumEvent := NullId;
  case Event is
    when CommentId =>
      null;
    when NewLineId =>
      if Debug then
        Status(SrcAuto, NomFich, LigneFich);
        Put_Line("Fichier " & NomFich & ", ligne " & Integer'Image(LigneFich));
      end if;
      null;
    when UndefId =>
      AddNew(StateList, Token);
      AddNew(ObjectList, "procedure Action" & Token & " is");
      AddNew(ObjectList, "  DumEvent : " & TEventStr & ";");
      AddNew(ObjectList, "");
      AddNew(ObjectList, "  begin");
      AddNew(ObjectList, "  DumEvent := " & NullEventStr & ";");
      CopyTo(DefaultInitList, ObjectList);
      State := ET2;
    when others =>
      Status(SrcAuto, NomFich, LigneFich);
      Put_Line("Erreur de syntaxe à la ligne " & Integer'Image(LigneFich) & " , " & TTokenId'Image(Event) & " , " & Token);
      State := stError;
    end case;
  Event := DumEvent;
  end;


procedure ActionET2 is
  DumEvent : TTokenId;

  begin
  DumEvent := NullId;
  case Event is
    when CommentId =>
      null;
    when NewLineId =>
      if Debug then
        Status(SrcAuto, NomFich, LigneFich);
        Put_Line("Fichier " & NomFich & ", ligne " & Integer'Image(LigneFich));
      end if;
      null;
    when InitId =>
      State := ET3;
    when EventId =>
      DumEvent := Event;
      AddNew(ObjectList,  "  case Event is");
      CopyTo(DefaultEventList, ObjectList);
      State := ET4;
    when others =>
      Status(SrcAuto, NomFich, LigneFich);
      Put_Line("Erreur de syntaxe à la ligne " & Integer'Image(LigneFich) & " , " & TTokenId'Image(Event) & " , " & Token);
      State := stError;
    end case;
  Event := DumEvent;
  end;


procedure ActionET3 is
  DumEvent : TTokenId;

  begin
  DumEvent := NullId;
  case Event is
    when CommentId =>
      null;
    when NewLineId =>
      if Debug then
        Status(SrcAuto, NomFich, LigneFich);
        Put_Line("Fichier " & NomFich & ", ligne " & Integer'Image(LigneFich));
      end if;
      null;
    when CallId | GosubId | ActionId | CarId =>
      DumEvent := Event;
      DefaultOutputList := ObjectList;
      declare
        LResult : Boolean;
      begin
        Automate(A1, DumEvent, Token, LResult, Debug);
        if LResult then
      null;
            else
          State := stError;
          end if;
        end;
    when EventId =>
      DumEvent := Event;
      AddNew(ObjectList,  "  case Event is");
      CopyTo(DefaultEventList, ObjectList);
      State := ET4;
    when others =>
      Status(SrcAuto, NomFich, LigneFich);
      Put_Line("Erreur de syntaxe à la ligne " & Integer'Image(LigneFich) & " , " & TTokenId'Image(Event) & " , " & Token);
      State := stError;
    end case;
  Event := DumEvent;
  end;


procedure ActionET4 is
  DumEvent : TTokenId;

  begin
  DumEvent := NullId;
  case Event is
    when CommentId =>
      null;
    when NewLineId =>
      if Debug then
        Status(SrcAuto, NomFich, LigneFich);
        Put_Line("Fichier " & NomFich & ", ligne " & Integer'Image(LigneFich));
      end if;
      null;
    when EventId =>
      DefaultOutputList := ObjectList;
      declare
        LResult : Boolean;
      begin
        Automate(EV1, DumEvent, Token, LResult, Debug);
        if LResult then
      null;
            else
          State := stError;
          end if;
        end;
    when FromId | EndId =>
      DumEvent := Event;
      if flDefaultDefault and then not flLocaldefault then
        CopyTo(DefaultDefaultList, ObjectList);
      end if;
      if not flLocaldefault and then not flDefaultDefault then
        AddNew(ObjectList,  "    when others =>");
        AddNew(ObjectList,  "      null;");
      end if;
      flLocalDefault := False;
      AddNew(ObjectList,  "    end case;");
      AddNew(ObjectList,  "  Event := DumEvent;");
      AddNew(ObjectList,  "  end;");
      AddNew(ObjectList, "");
      AddNew(ObjectList, "");
      State := stQuit;
    when others =>
      Status(SrcAuto, NomFich, LigneFich);
      Put_Line("Erreur de syntaxe à la ligne " & Integer'Image(LigneFich) & " , " & TTokenId'Image(Event) & " , " & Token);
      State := stError;
    end case;
  Event := DumEvent;
  end;


procedure ActionEV1 is
  DumEvent : TTokenId;

  begin
  DumEvent := NullId;
  case Event is
    when CommentId =>
      null;
    when NewLineId =>
      if Debug then
        Status(SrcAuto, NomFich, LigneFich);
        Put_Line("Fichier " & NomFich & ", ligne " & Integer'Image(LigneFich));
      end if;
      null;
    when UndefId =>
      Add(DefaultOutputList, "    when " & Token);
      AddUniq(EventList, Token);
      State := EV2;
    when DefaultId =>
      flLocalDefault := True;
      Add(DefaultOutputList,  "    when others");
      State := EV2;
    when others =>
      Status(SrcAuto, NomFich, LigneFich);
      Put_Line("Erreur de syntaxe à la ligne " & Integer'Image(LigneFich) & " , " & TTokenId'Image(Event) & " , " & Token);
      State := stError;
    end case;
  Event := DumEvent;
  end;


procedure ActionEV2 is
  DumEvent : TTokenId;

  begin
  DumEvent := NullId;
  case Event is
    when CommentId =>
      null;
    when NewLineId =>
      if Debug then
        Status(SrcAuto, NomFich, LigneFich);
        Put_Line("Fichier " & NomFich & ", ligne " & Integer'Image(LigneFich));
      end if;
      null;
    when VirgId =>
      Add(DefaultOutputList, " | ");
      State := EV3;
    when PointPointId =>
      Add(DefaultOutputList, " .. ");
      State := EV3;
    when PlusId =>
      AddNew(DefaultOutputList,  " =>");
      AddNew(DefaultOutputList,  "      DumEvent := Event;");
      State := EV4;
    when ToId =>
      AddNew(DefaultOutputList,  " =>");
      State := EV5;
    when others =>
      Status(SrcAuto, NomFich, LigneFich);
      Put_Line("Erreur de syntaxe à la ligne " & Integer'Image(LigneFich) & " , " & TTokenId'Image(Event) & " , " & Token);
      State := stError;
    end case;
  Event := DumEvent;
  end;


procedure ActionEV3 is
  DumEvent : TTokenId;

  begin
  DumEvent := NullId;
  case Event is
    when CommentId =>
      null;
    when NewLineId =>
      if Debug then
        Status(SrcAuto, NomFich, LigneFich);
        Put_Line("Fichier " & NomFich & ", ligne " & Integer'Image(LigneFich));
      end if;
      null;
    when UndefId =>
      Add(DefaultOutputList, Token);
      AddUniq(EventList, Token);
      State := EV2;
    when others =>
      Status(SrcAuto, NomFich, LigneFich);
      Put_Line("Erreur de syntaxe à la ligne " & Integer'Image(LigneFich) & " , " & TTokenId'Image(Event) & " , " & Token);
      State := stError;
    end case;
  Event := DumEvent;
  end;


procedure ActionEV4 is
  DumEvent : TTokenId;

  begin
  DumEvent := NullId;
  case Event is
    when CommentId =>
      null;
    when NewLineId =>
      if Debug then
        Status(SrcAuto, NomFich, LigneFich);
        Put_Line("Fichier " & NomFich & ", ligne " & Integer'Image(LigneFich));
      end if;
      null;
    when ToId =>
      State := EV5;
    when others =>
      Status(SrcAuto, NomFich, LigneFich);
      Put_Line("Erreur de syntaxe à la ligne " & Integer'Image(LigneFich) & " , " & TTokenId'Image(Event) & " , " & Token);
      State := stError;
    end case;
  Event := DumEvent;
  end;


procedure ActionEV5 is
  DumEvent : TTokenId;

  begin
  DumEvent := NullId;
  case Event is
    when CommentId =>
      null;
    when NewLineId =>
      if Debug then
        Status(SrcAuto, NomFich, LigneFich);
        Put_Line("Fichier " & NomFich & ", ligne " & Integer'Image(LigneFich));
      end if;
      null;
    when UndefId =>
      StateToStr := Token;
      State := EV6;
    when OutId =>
      StateToStr := To_Unbounded_String("stQuit");
      State := EV6;
    when ErrId =>
      StateToStr := To_Unbounded_String("stError");
      State := EV6;
    when SameId =>
      StateToStr := Null_Unbounded_String;
      State := EV6;
    when others =>
      Status(SrcAuto, NomFich, LigneFich);
      Put_Line("Erreur de syntaxe à la ligne " & Integer'Image(LigneFich) & " , " & TTokenId'Image(Event) & " , " & Token);
      State := stError;
    end case;
  Event := DumEvent;
  end;


procedure ActionEV6 is
  DumEvent : TTokenId;

  begin
  DumEvent := NullId;
  case Event is
    when CommentId =>
      null;
    when NewLineId =>
      if Debug then
        Status(SrcAuto, NomFich, LigneFich);
        Put_Line("Fichier " & NomFich & ", ligne " & Integer'Image(LigneFich));
      end if;
      null;
    when EventId | EndId | FromId =>
      DumEvent := Event;
      if StateToStr /= "" then
        AddNew(DefaultOutputList, "      State := " & StateToStr & ";");
      else
        AddNew(DefaultOutputList, "      null;");
      end if;
      if flGosub then
        AddNew(DefaultOutputList, "            else");
        AddNew(DefaultOutputList, "          State := stError;");
        AddNew(DefaultOutputList, "          end if;");
        AddNew(DefaultOutputList, "        end;");
        flGosub := False;
      end if;
      State := stQuit;
    when CallId | GosubId | ActionId | CarId =>
      DumEvent := Event;
      declare
        LResult : Boolean;
      begin
        Automate(A1, DumEvent, Token, LResult, Debug);
        if LResult then
      null;
            else
          State := stError;
          end if;
        end;
    when others =>
      Status(SrcAuto, NomFich, LigneFich);
      Put_Line("Erreur de syntaxe à la ligne " & Integer'Image(LigneFich) & " , " & TTokenId'Image(Event) & " , " & Token);
      State := stError;
    end case;
  Event := DumEvent;
  end;


procedure ActionA1 is
  DumEvent : TTokenId;

  begin
  DumEvent := NullId;
  case Event is
    when CommentId =>
      null;
    when NewLineId =>
      if Debug then
        Status(SrcAuto, NomFich, LigneFich);
        Put_Line("Fichier " & NomFich & ", ligne " & Integer'Image(LigneFich));
      end if;
      null;
    when CallId =>
      State := A2;
    when GosubId =>
      State := A3;
    when ActionId =>
      State := A4;
    when CarId =>
      DumEvent := Event;
      State := A4;
    when others =>
      Status(SrcAuto, NomFich, LigneFich);
      Put_Line("Erreur de syntaxe à la ligne " & Integer'Image(LigneFich) & " , " & TTokenId'Image(Event) & " , " & Token);
      State := stError;
    end case;
  Event := DumEvent;
  end;


procedure ActionA2 is
  DumEvent : TTokenId;

  begin
  DumEvent := NullId;
  case Event is
    when CommentId =>
      null;
    when NewLineId =>
      if Debug then
        Status(SrcAuto, NomFich, LigneFich);
        Put_Line("Fichier " & NomFich & ", ligne " & Integer'Image(LigneFich));
      end if;
      null;
    when UndefId =>
      AddNew(DefaultOutputList, "      declare");
      AddNew(DefaultOutputList, "        LResult : Boolean;");
      AddNew(DefaultOutputList, "      begin");
      AddNew(DefaultOutputList, "        Start" & Token & "(LResult, Debug);");
      AddNew(DefaultOutputList, "        if LResult then");
      AddUniq(CallUnitList, Token);
      flGosub := True;
      State := stQuit;
    when others =>
      Status(SrcAuto, NomFich, LigneFich);
      Put_Line("Erreur de syntaxe à la ligne " & Integer'Image(LigneFich) & " , " & TTokenId'Image(Event) & " , " & Token);
      State := stError;
    end case;
  Event := DumEvent;
  end;


procedure ActionA3 is
  DumEvent : TTokenId;

  begin
  DumEvent := NullId;
  case Event is
    when CommentId =>
      null;
    when NewLineId =>
      if Debug then
        Status(SrcAuto, NomFich, LigneFich);
        Put_Line("Fichier " & NomFich & ", ligne " & Integer'Image(LigneFich));
      end if;
      null;
    when UndefId =>
      AddNew(DefaultOutputList, "      declare");
      AddNew(DefaultOutputList, "        LResult : Boolean;");
      AddNew(DefaultOutputList, "      begin");
      AddNew(DefaultOutputList, "        Automate(" & Token & ", DumEvent, " & EventDesStr &
                                                  ", LResult, Debug);");
      AddNew(DefaultOutputList, "        if LResult then");
      flGosub := True;
      State := stQuit;
    when others =>
      Status(SrcAuto, NomFich, LigneFich);
      Put_Line("Erreur de syntaxe à la ligne " & Integer'Image(LigneFich) & " , " & TTokenId'Image(Event) & " , " & Token);
      State := stError;
    end case;
  Event := DumEvent;
  end;


procedure ActionA4 is
  DumEvent : TTokenId;

  begin
  DumEvent := NullId;
  case Event is
    when CommentId =>
      null;
    when NewLineId =>
      if Debug then
        Status(SrcAuto, NomFich, LigneFich);
        Put_Line("Fichier " & NomFich & ", ligne " & Integer'Image(LigneFich));
      end if;
      null;
    when CarId =>
      AddNew(DefaultOutputList, "  " & Token);
      State := stQuit;
    when others =>
      Status(SrcAuto, NomFich, LigneFich);
      Put_Line("Erreur de syntaxe à la ligne " & Integer'Image(LigneFich) & " , " & TTokenId'Image(Event) & " , " & Token);
      State := stError;
    end case;
  Event := DumEvent;
  end;


procedure ActionD1 is
  DumEvent : TTokenId;

  begin
  DumEvent := NullId;
  case Event is
    when CommentId =>
      null;
    when NewLineId =>
      if Debug then
        Status(SrcAuto, NomFich, LigneFich);
        Put_Line("Fichier " & NomFich & ", ligne " & Integer'Image(LigneFich));
      end if;
      null;
    when InitId =>
      State := D2;
    when EventId =>
      DumEvent := Event;
      State := D4;
    when others =>
      Status(SrcAuto, NomFich, LigneFich);
      Put_Line("Erreur de syntaxe à la ligne " & Integer'Image(LigneFich) & " , " & TTokenId'Image(Event) & " , " & Token);
      State := stError;
    end case;
  Event := DumEvent;
  end;


procedure ActionD2 is
  DumEvent : TTokenId;

  begin
  DumEvent := NullId;
  case Event is
    when CommentId =>
      null;
    when NewLineId =>
      if Debug then
        Status(SrcAuto, NomFich, LigneFich);
        Put_Line("Fichier " & NomFich & ", ligne " & Integer'Image(LigneFich));
      end if;
      null;
    when CallId | GosubId | ActionId | CarId =>
      DumEvent := Event;
      DefaultOutputList := DefaultInitList;
      declare
        LResult : Boolean;
      begin
        Automate(A1, DumEvent, Token, LResult, Debug);
        if LResult then
      State := D3;
            else
          State := stError;
          end if;
        end;
    when others =>
      Status(SrcAuto, NomFich, LigneFich);
      Put_Line("Erreur de syntaxe à la ligne " & Integer'Image(LigneFich) & " , " & TTokenId'Image(Event) & " , " & Token);
      State := stError;
    end case;
  Event := DumEvent;
  end;


procedure ActionD3 is
  DumEvent : TTokenId;

  begin
  DumEvent := NullId;
  case Event is
    when CommentId =>
      null;
    when NewLineId =>
      if Debug then
        Status(SrcAuto, NomFich, LigneFich);
        Put_Line("Fichier " & NomFich & ", ligne " & Integer'Image(LigneFich));
      end if;
      null;
    when FromId =>
      DumEvent := Event;
      State := stQuit;
    when CallId | GosubId | ActionId | CarId =>
      DumEvent := Event;
      DefaultOutputList := DefaultInitList;
      declare
        LResult : Boolean;
      begin
        Automate(A1, DumEvent, Token, LResult, Debug);
        if LResult then
      null;
            else
          State := stError;
          end if;
        end;
    when EventId =>
      DumEvent := Event;
      State := D4;
    when others =>
      Status(SrcAuto, NomFich, LigneFich);
      Put_Line("Erreur de syntaxe à la ligne " & Integer'Image(LigneFich) & " , " & TTokenId'Image(Event) & " , " & Token);
      State := stError;
    end case;
  Event := DumEvent;
  end;


procedure ActionD4 is
  DumEvent : TTokenId;

  begin
  DumEvent := NullId;
  case Event is
    when CommentId =>
      null;
    when NewLineId =>
      if Debug then
        Status(SrcAuto, NomFich, LigneFich);
        Put_Line("Fichier " & NomFich & ", ligne " & Integer'Image(LigneFich));
      end if;
      null;
    when EventId =>
      State := D5;
    when FromId =>
      DumEvent := Event;
      State := stQuit;
    when others =>
      Status(SrcAuto, NomFich, LigneFich);
      Put_Line("Erreur de syntaxe à la ligne " & Integer'Image(LigneFich) & " , " & TTokenId'Image(Event) & " , " & Token);
      State := stError;
    end case;
  Event := DumEvent;
  end;


procedure ActionD5 is
  DumEvent : TTokenId;

  begin
  DumEvent := NullId;
  case Event is
    when CommentId =>
      null;
    when NewLineId =>
      if Debug then
        Status(SrcAuto, NomFich, LigneFich);
        Put_Line("Fichier " & NomFich & ", ligne " & Integer'Image(LigneFich));
      end if;
      null;
    when UndefId =>
      DefaultOutputList := DefaultEventList;
      Add(DefaultOutputList, "    when " & Token);
      AddUniq(EventList, Token);
      declare
        LResult : Boolean;
      begin
        Automate(EV2, DumEvent, Token, LResult, Debug);
        if LResult then
      State := D4;
            else
          State := stError;
          end if;
        end;
    when DefaultId =>
      DefaultOutputList := DefaultDefaultList;
      Add(DefaultOutputList, "    when others");
      flDefaultDefault := True;
      declare
        LResult : Boolean;
      begin
        Automate(EV2, DumEvent, Token, LResult, Debug);
        if LResult then
      State := D4;
            else
          State := stError;
          end if;
        end;
    when others =>
      Status(SrcAuto, NomFich, LigneFich);
      Put_Line("Erreur de syntaxe à la ligne " & Integer'Image(LigneFich) & " , " & TTokenId'Image(Event) & " , " & Token);
      State := stError;
    end case;
  Event := DumEvent;
  end;


procedure ActionFin is
  DumEvent : TTokenId;

  begin
  DumEvent := NullId;
  case Event is
    when CommentId =>
      null;
    when NewLineId =>
      if Debug then
        Status(SrcAuto, NomFich, LigneFich);
        Put_Line("Fichier " & NomFich & ", ligne " & Integer'Image(LigneFich));
      end if;
      null;
    when EotId =>
      State := stQuit;
    when others =>
      Status(SrcAuto, NomFich, LigneFich);
      Put_Line("Erreur de syntaxe à la ligne " & Integer'Image(LigneFich) & " , " & TTokenId'Image(Event) & " , " & Token);
      State := stError;
    end case;
  Event := DumEvent;
  end;


  begin
  Result := Event = NullId;
  while (State /= stError) and (State /= stQuit) loop
    while Event = NullId loop
      ReadToken(Event, Token);
    end loop;
    if Debug then
      Put(TState'Image(State) & "; " & TTokenId'Image(Event));
      if not Result then
        Put("+");
        Result := True;
      end if;
      Put_Line("; " & Token);
    end if;
    case State is
      when DA1 => ActionDA1;
      when DA2 => ActionDA2;
      when DA3 => ActionDA3;
      when DA5 => ActionDA5;
      when ET1 => ActionET1;
      when ET2 => ActionET2;
      when ET3 => ActionET3;
      when ET4 => ActionET4;
      when EV1 => ActionEV1;
      when EV2 => ActionEV2;
      when EV3 => ActionEV3;
      when EV4 => ActionEV4;
      when EV5 => ActionEV5;
      when EV6 => ActionEV6;
      when A1 => ActionA1;
      when A2 => ActionA2;
      when A3 => ActionA3;
      when A4 => ActionA4;
      when D1 => ActionD1;
      when D2 => ActionD2;
      when D3 => ActionD3;
      when D4 => ActionD4;
      when D5 => ActionD5;
      when Fin => ActionFin;
      when others =>
        null;
      end case;
    end loop;
  Result := State /= stError;
  end Automate;

procedure StartSrcSeq(Result : out Boolean; Debug : Boolean := False) is
  Event : TTokenId;
  Token : TTokenStr;
  begin
  ReadToken(Event, Token);
  Automate(DA1, Event, Token, Result, Debug);
  end StartSrcSeq;

end SrcSeq;
