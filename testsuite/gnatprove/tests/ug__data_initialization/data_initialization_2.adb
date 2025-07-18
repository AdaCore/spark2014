package body Data_Initialization_2 with SPARK_Mode is

   procedure P_String (L : out Natural; S : out String) is
   begin
      L := S'Length;
      S := (others => ' ');
   end P_String;

   procedure P_Option (B : out Boolean; O : out Int_Option) is
   begin
      B := O.Present;
      if not O'Constrained or else not O.Present then
         O := (Present => False);
      else
         O := (True, 12);
      end if;
   end P_Option;

  procedure Call_P_Option (B_in : Boolean; B_out : out Boolean) is
    Tmp : Int_Option (B_in); -- the discriminant of Tmp cannot be modified
    pragma Assert (Tmp'Constrained);
  begin
    P_Option (B_out, Tmp);
  end Call_P_Option;

end;
