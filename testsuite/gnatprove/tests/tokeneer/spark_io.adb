------------------------------------------------------------------
-- Tokeneer ID Station Support Software
--
-- Copyright (2003) United States Government, as represented
-- by the Director, National Security Agency. All rights reserved.
--
-- This material was originally developed by Praxis High Integrity
-- Systems Ltd. under contract to the National Security Agency.
------------------------------------------------------------------

pragma Ada_95;
package body Spark_IO is
   pragma SPARK_Mode (Off);
-- File Management

  procedure Create (File         :    out File_Type;
                    Name_Of_File : in     String;
                    Form_Of_File : in     String;
                    Status       :    out File_Status)
  is
  begin
    Status := Ok;
    File.File := new Ada.Text_IO.File_Type;
    Ada.Text_IO.Create ( File.File.all, Ada.Text_IO.Out_File,
                     Name_Of_File,  Form_Of_File);
  exception
    when Ada.Text_IO.Status_Error  => Status := Status_Error;
    when Ada.Text_IO.Name_Error    => Status := Name_Error;
    when Ada.Text_IO.Use_Error     => Status := Use_Error;
    when Ada.Text_IO.Device_Error  => Status := Device_Error;
    when Standard.Storage_Error    => Status := Storage_Error;
    when Standard.Program_Error    => Status := Program_Error;
  end Create;

  procedure Open (File         :    out File_Type;
                  Mode_Of_File : in     File_Mode;
                  Name_Of_File : in     String;
                  Form_Of_File : in     String;
                  Status       :    out File_Status)
  is
    Fmode : Ada.Text_IO.File_Mode;
  begin
    case Mode_Of_File is
      when In_File     => Fmode := Ada.Text_IO.In_File;
      when Out_File    => Fmode := Ada.Text_IO.Out_File;
      when Append_File => Fmode := Ada.Text_IO.Append_File;
    end case;
    Status := Ok;
    File.File := new Ada.Text_IO.File_Type;
    Ada.Text_IO.Open( File.File.all, Fmode, Name_Of_File, Form_Of_File);
  exception
    when Ada.Text_IO.Status_Error  => Status := Status_Error;
    when Ada.Text_IO.Name_Error    => Status := Name_Error;
    when Ada.Text_IO.Use_Error     => Status := Use_Error;
    when Ada.Text_IO.Device_Error  => Status := Device_Error;
    when Standard.Storage_Error    => Status := Storage_Error;
    when Standard.Program_Error    => Status := Program_Error;
  end Open;

  procedure Close (File   : in     File_Type;
                   Status :    out File_Status)
  is
  begin
    Ada.Text_IO.Close( File.File.all);
    Status := Ok;
  exception
    when Constraint_Error         => Status := Use_Error;
    when Ada.Text_IO.Status_Error => Status := Status_Error;
    when Ada.Text_IO.Device_Error => Status := Device_Error;
    when Standard.Storage_Error   => Status := Storage_Error;
    when Standard.Program_Error   => Status := Program_Error;
  end Close;

  procedure Delete (File   : in     File_Type;
                    Status :    out File_Status)
  is
  begin
    Ada.Text_IO.Delete( File.File.all);
    Status := Ok;
  exception
    when Ada.Text_IO.Status_Error => Status := Status_Error;
    when Ada.Text_IO.Use_Error    => Status := Use_Error;
    when Constraint_Error         => Status := Use_Error;
    when Ada.Text_IO.Device_Error => Status := Device_Error;
    when Standard.Storage_Error   => Status := Storage_Error;
    when Standard.Program_Error   => Status := Program_Error;
  end Delete;

  procedure Reset( File         : in out File_Type;
                   Mode_Of_File : in     File_Mode;
                   Status       :    out File_Status)
  is
    Fmode : Ada.Text_IO.File_Mode;
  begin
    case Mode_Of_File is
      when In_File     => Fmode := Ada.Text_IO.In_File;
      when Out_File    => Fmode := Ada.Text_IO.Out_File;
      when Append_File => Fmode := Ada.Text_IO.Append_File;
    end case;
    Ada.Text_IO.Reset( File.File.all, Fmode);
    Status := Ok;
  exception
    when Ada.Text_IO.Status_Error => Status := Status_Error;
    when Ada.Text_IO.Use_Error    => Status := Use_Error;
    when Ada.Text_IO.Device_Error => Status := Device_Error;
    when Standard.Storage_Error   => Status := Storage_Error;
    when Standard.Program_Error   => Status := Program_Error;
  end Reset;

  function Valid_File (File : File_Type) return Boolean
  is
    Valid : Boolean;
  begin
    case File.IO_Sort is
      when Stdin     => Valid := True;
      when Stdout    => Valid := True;
      when NamedFile => Valid := (File.File /= null);
    end case;
    return Valid;
  end Valid_File;

  function File_Ref (File : File_Type) return Ada.Text_IO.File_Type
  is
  begin
    case File.IO_Sort is
      when Stdin     => return Ada.Text_IO.Standard_Input;
      when Stdout    => return Ada.Text_IO.Standard_Output;
      when NamedFile =>
         pragma Warnings (Off, "cannot copy object of a limited type in Ada 2005");
         return File.File.all;
         pragma Warnings (On, "cannot copy object of a limited type in Ada 2005");
    end case;
  end File_Ref;

  function Is_Open( File : File_Type) return Boolean
  is
  begin
    return Valid_File( File) and then
           Ada.Text_IO.Is_Open( File_Ref( File));
  end Is_Open;

  function Mode( File : File_Type) return File_Mode
  is
    Fmode : File_Mode;
  begin
    if Is_Open( File) and then
       Ada.Text_IO.Is_Open( File_Ref( File)) then
      case Ada.Text_IO.Mode( File_Ref( File)) is
        when Ada.Text_IO.In_File     => Fmode := In_File;
        when Ada.Text_IO.Out_File    => Fmode := Out_File;
        when Ada.Text_IO.Append_File => Fmode := Append_File;
      end case;
    else
      Fmode := In_File;
    end if;
    return Fmode;
  end Mode;

  function Is_In( File : File_Type) return Boolean
  is
  begin
    return Is_Open( File) and then Mode( File) = In_File;
  end Is_In;

  function Is_Out( File : File_Type) return Boolean
  is
  begin
    return Is_Open( File) and then (Mode( File) = Out_File or
                                    Mode( File) = Append_File);
  end Is_Out;

  procedure Name( File         : in     File_Type;
                  Name_Of_File :    out String;
                  Stop         :    out Natural)
  is
  begin
    if Is_Open( File) then
      declare
        Fn : constant String := Ada.Text_IO.Name( File_Ref( File));
      begin
        if Name_Of_File'Length >= Fn'Length then
          Name_Of_File( Fn'Range) := Fn;
          Stop := Fn'Length;
        else
          Name_Of_File := Fn(Name_Of_File'Range);
          Stop := Name_Of_File'Length;
        end if;
      end;
    else
      Stop := Name_Of_File'First - 1;
    end if;
  exception
    when others => Stop := Name_Of_File'First - 1;
  end Name;

  procedure Form(File         : in     File_Type;
                 Form_Of_File :    out String;
                 Stop         :    out Natural)
  is
  begin
    if Is_Open( File) then
      declare
        Fm : constant string := Ada.Text_IO.Form( File_Ref( File));
      begin
        if Form_Of_File'Length >= Fm'Length then
          Form_Of_File( Fm'Range) := Fm;
          Stop := Fm'Length;
        else
          Form_Of_File := Fm( Form_Of_File'Range);
          Stop := Form_Of_File'Length;
        end if;
      end;
    else
      Stop := Form_Of_File'First - 1;
    end if;
  exception
    when others => Stop := Form_Of_File'First - 1;
  end Form;

-- Line and file terminator control

  function P_To_PC( P : Positive) return Ada.Text_IO.Positive_Count
  is
    PC : Ada.Text_IO.Positive_Count;
  begin
    if P > Positive( Ada.Text_IO.Positive_Count'Last) then
      PC := Ada.Text_IO.Positive_Count'Last;
    else
      PC := Ada.Text_IO.Positive_Count( P);
    end if;
    return PC;
  end P_To_PC;

  function PC_To_P(PC : Ada.Text_IO.Positive_Count) return Positive
  is
  begin
    return Positive( PC);
  end PC_To_P;

  procedure New_Line(File    : in File_Type;
                     Spacing : in Positive)
  is
    Gap    : Ada.Text_IO.Positive_Count;
  begin
    if Is_Out( File) then
      Gap := P_To_PC( Spacing);
      Ada.Text_IO.New_Line( File_Ref( File), Gap);
    end if;
  exception
    when others => null;
  end New_Line;

  procedure Skip_Line( File    : in File_Type;
                       Spacing : in Positive)
  is
    Gap    : Ada.Text_IO.Positive_Count;
  begin
    if Is_In( File) then
      Gap := P_To_PC( Spacing);
      Ada.Text_IO.Skip_Line( File_Ref( File), Gap);
    end if;
  exception
    when others => null;
  end Skip_Line;

  procedure New_Page ( File : in File_Type)
  is
  begin
    if Is_Out( File) then
      Ada.Text_IO.New_Page( File_Ref( File));
    end if;
  exception
    when others => null;
  end New_Page;

  function End_Of_Line( File : File_Type) return Boolean
  is
    EOLN : Boolean;
  begin
    if Is_In( File) then
      EOLN := Ada.Text_IO.End_Of_Line( File_Ref( File));
    else
      EOLN := False;
    end if;
    return EOLN;
  end End_Of_Line;

  function End_Of_File( File : File_Type) return Boolean
  is
    EOF : Boolean;
  begin
    if Is_In( File) then
      EOF := Ada.Text_IO.End_Of_File( File_Ref( File));
    else
      EOF := True;
    end if;
    return EOF;
  end End_Of_File;

  procedure Set_Col (File : in File_Type;
                     Posn : in Positive)
  is
    Col    : Ada.Text_IO.Positive_Count;
  begin
    if Is_Open( File) then
      Col := P_To_PC( Posn);
      Ada.Text_IO.Set_Col( File_Ref( File), Col);
    end if;
  exception
    when others => null;
  end Set_Col;

  procedure Set_In_File_Col (File : in File_Type;
                             Posn : in Positive)
  is
  begin
    if Is_In( File ) then
       Set_Col( File, Posn);
    end if;
  end Set_In_File_Col;

  procedure Set_Out_File_Col (File : in File_Type;
                              Posn : in Positive)
  is
  begin
    if Is_Out( File ) then
       Set_Col( File, Posn);
    end if;
  end Set_Out_File_Col;

  function Col (File : File_Type) return Positive
  is
    Posn : Positive;
    Col  : Ada.Text_IO.Positive_Count;
  begin
    if Is_Open( File) then
      Col := Ada.Text_IO.Col( File_Ref( File));
      Posn := Pc_To_P( Col);
    else
      Posn := 1;
    end if;
    return Posn;
  exception
    when Ada.Text_IO.Status_Error => return 1;
    when Ada.Text_IO.Layout_Error => return PC_To_P( Ada.Text_IO.Count'Last);
    when Ada.Text_IO.Device_Error => return 1;
    when Standard.Storage_Error   => return 1;
    when Standard.Program_Error   => return 1;
  end Col;

  function In_File_Col (File : File_Type) return Positive
  is
  begin
    if Is_In (File) then
       return Col (File);
    else
       return 1;
    end if;
  end In_File_Col;

  function Out_File_Col (File : File_Type) return Positive
  is
  begin
    if Is_Out (File) then
       return Col (File);
    else
       return 1;
    end if;
  end Out_File_Col;

  function Line (File : File_Type) return Positive
  is
    Posn : Positive;
    Line : Ada.Text_IO.Positive_Count;
  begin
    if Is_Open( File) then
      Line := Ada.Text_IO.Line( File_Ref( File));
      Posn := PC_To_P( Line);
    else
      Posn := 1;
    end if;
    return Posn;
  exception
    when Ada.Text_IO.Status_Error => return 1;
    when Ada.Text_IO.Layout_Error => return PC_To_P( Ada.Text_IO.Count'Last);
    when Ada.Text_IO.Device_Error => return 1;
    when Standard.Storage_Error   => return 1;
    when Standard.Program_Error   => return 1;
  end Line;

  function In_File_Line (File : File_Type) return Positive
  is
  begin
     if Is_In (File) then
        return Line (File);
     else
        return 1;
     end if;
  end In_File_Line;

  function Out_File_Line (File : File_Type) return Positive
  is
  begin
     if Is_Out (File) then
        return Line (File);
     else
        return 1;
     end if;
  end Out_File_Line;


-- Character IO

  procedure Get_Char (File : in     File_Type;
                      Item :    out Character)
  is
  begin
    if Is_In( File) then
      Ada.Text_IO.Get( File_Ref( File), Item);
    else
      Item := Character'First;
    end if;
  exception
    when others => null;
  end Get_Char;

  procedure Put_Char (File : in File_Type;
                      Item : in Character)
  is
  begin
    if Is_Out( File) then
      Ada.Text_IO.Put( File_Ref( File), Item);
    end if;
  exception
    when others => null;
  end Put_Char;


-- String IO

  procedure Get_String (File : in     File_Type;
                        Item :    out String;
                        Stop :    out Natural)
  is
    LSTP : Natural;
  begin
    if Is_In( File) then
      LSTP := Item'First - 1;
      loop
        exit when End_Of_File( File);
        LSTP := LSTP + 1;
        Get_Char( File, Item(LSTP));
        exit when LSTP = Item'Last;
      end loop;
      Stop := LSTP;
    else
      Stop := Item'First - 1;
    end if;
  end Get_String;

  -- CFR 718 The behaviour of Put_String is now as follows:
  -- If Stop is 0 then all characters in Item are output.
  -- If Stop <= Item'Last then output Item(Item'First .. Stop).
  -- If Stop > Item'Last then output all characters in Item, then pad with
  -- spaces to width specified by Stop.
  procedure Put_String (File : in File_Type;
                        Item : in String;
                        Stop : in Natural)
  is
    Pad : Natural;
  begin

    if Is_Out( File) then

      if Stop = 0 then
        Ada.Text_IO.Put( File_Ref( File), Item);
      elsif Stop <= Item'Last then
        Ada.Text_IO.Put( File_Ref( File), Item( Item'First .. Stop));
      else
        Pad := Stop - Item'Last;
        Ada.Text_IO.Put( File_Ref( File), Item);
        while Pad > 0 loop
          Ada.Text_IO.Put( File_Ref( File), ' ');
          Pad := Pad - 1;
        end loop;
      end if;

    end if;

  exception
    when others => null;
  end Put_String;

  procedure Get_Line (File : in     File_Type;
                      Item :    out String;
                      Stop :    out Natural)
  is
  begin
    if Is_In( File) then
      Ada.Text_IO.Get_Line( File_Ref( File), Item, Stop);
    else
      Stop := Item'First - 1;
    end if;
  exception
    when others => Stop := Item'First - 1;
  end Get_Line;

  procedure Put_Line (File : in File_Type;
                      Item : in String;
                      Stop : in Natural)
  is
    ES : Positive;
  begin
    if Stop = 0 then
      ES := Item'Last;
    else
      ES := Stop;
    end if;
    if Is_Out( File) then
      Ada.Text_IO.Put_Line( File_Ref( File), Item( Item'First .. ES));
    end if;
  exception
    when others => null;
  end Put_Line;


-- Integer IO

  package Integer_IO is new Ada.Text_IO.Integer_IO( Integer);

  procedure Get_Integer (File  : in     File_Type;
                         Item  :    out Integer;
                         Width : in     Natural;
                         Read  :    out Boolean)
  is
  begin
    if Is_In( File) then
      Integer_IO.Get( File_Ref( File), Item, Width);
      Read := True;
    else
      Read := False;
    end if;
  exception
    when others => Read := False;
  end Get_Integer;

  procedure Put_Integer (File  : in File_Type;
                         Item  : in Integer;
                         Width : in Natural;
                         Base  : in Number_Base)
  is
  begin
    if Is_Out( File) then
      Integer_IO.Put( File_Ref( File), Item, Width, Base);
    end if;
  exception
    when others => null;
  end Put_Integer;

  procedure Get_Int_From_String (Source    : in     String;
                                 Item      :    out Integer;
                                 Start_Pos : in     Positive;
                                 Stop      :    out Natural)
  is
  begin
    Integer_IO.Get( Source( Start_Pos..Source'Last), Item, Stop);
  exception
    when others => Stop := Start_Pos - 1;
  end Get_Int_From_String;

  procedure Put_Int_To_String (Dest      : in out String;
                               Item      : in     Integer;
                               Start_Pos : in     Positive;
                               Base      : in     Number_Base)
  is
  begin
    Integer_IO.Put( Dest( Start_Pos..Dest'Last), Item, Base);
  exception
    when others => null;
  end Put_Int_To_String;


-- Float IO

  package Real_IO is new Ada.Text_IO.Float_IO( Float);

  procedure Get_Float (File  : in     File_Type;
                       Item  :    out Float;
                       Width : in     Natural;
                       Read  :    out Boolean)
  is
  begin
    if Is_In( File) then
      Real_IO.Get( File_Ref( File), Item, Width);
      Read := True;
    else
      Read := False;
    end if;
  exception
    when others => Read := False;
  end Get_Float;

  procedure Put_Float (File : in File_Type;
                       Item : in Float;
                       Fore : in Natural;
                       Aft  : in Natural;
                       Exp  : in Natural)
  is
  begin
    if Is_Out( File) then
      Real_IO.Put( File_Ref( File), Item, Fore, Aft, Exp);
    end if;
  exception
    when others => null;
  end Put_Float;

  procedure Get_Float_From_String (Source    : in     String;
                                   Item      :    out Float;
                                   Start_Pos : in     Positive;
                                   Stop      :    out Natural)
  is
  begin
    Real_IO.Get( Source( Start_Pos..Source'Last), Item, Stop);
  exception
    when others => Stop := Start_Pos - 1;
  end Get_Float_From_String;

  procedure Put_Float_To_String (Dest      : in out String;
                                 Item      : in     Float;
                                 Start_Pos : in     Positive;
                                 Aft       : in     Natural;
                                 Exp       : in     Natural)
  is
  begin
    Real_IO.Put( Dest( Start_Pos..Dest'Last), Item, Aft, Exp);
  exception
    when others => null;
  end Put_Float_To_String;

end Spark_IO;
