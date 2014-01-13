pragma Ada_95;
package body Spark_IO
is
   pragma SPARK_Mode (Off);
-- File Management

  function Valid_File(File : File_Type) return Boolean
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

  function File_Ref( File : File_Type) return Ada.Text_IO.File_Type
  is
  begin
    case File.IO_Sort is
      when Stdin     => return Ada.Text_IO.Standard_Input;
      when Stdout    => return Ada.Text_IO.Standard_Output;
      when NamedFile => return File.File.all;
    end case;
  end File_Ref;

  function Is_Open(File : File_Type) return Boolean
  is
  begin
    return Valid_File(File) and then
           Ada.Text_IO.Is_Open (File_Ref (File));
  end Is_Open;

  function Mode(File : File_Type) return File_Mode
  is
    Fmode : File_Mode;
  begin
    if Is_Open( File) and then
       Ada.Text_IO.Is_Open(File_Ref (File)) then
      case Ada.Text_IO.Mode(File_Ref (File)) is
        when Ada.Text_IO.In_File     => Fmode := In_File;
        when Ada.Text_IO.Out_File    => Fmode := Out_File;
        when Ada.Text_IO.Append_File => Fmode := Append_File;
      end case;
    else
      Fmode := In_File;
    end if;
    return Fmode;
  end Mode;

  function Is_In(File : File_Type) return Boolean
  is
  begin
    return Is_Open(File) and then Mode(File) = In_File;
  end Is_In;

  function P_To_PC (P : Positive) return Ada.Text_IO.Positive_Count
  is
    PC : Ada.Text_IO.Positive_Count;
  begin
    if P > Positive (Ada.Text_IO.Positive_Count'Last) then
      PC := Ada.Text_IO.Positive_Count'Last;
    else
      PC := Ada.Text_IO.Positive_Count(P);
    end if;
    return PC;
  end;

  function PC_To_P (PC : Ada.Text_IO.Positive_Count) return Positive
  is
  begin
    return Positive (PC);
  end;

  function Col(File : File_Type) return Positive
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

  function In_File_Col(File : File_Type) return Positive
  is
  begin
    if Is_In (File) then
       return Col (File);
    else
       return 1;
    end if;
  end In_File_Col;

end Spark_IO;
