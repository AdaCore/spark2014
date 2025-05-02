package Data_Initialization_2 with SPARK_Mode is

   procedure P_String (L : out Natural; S : out String) with
     Depends => ((L, S) => S);

   type Int_Option (Present : Boolean := False) is record
      case Present is
      when True =>
         Value : Integer;
      when False =>
         null;
      end case;
   end record;

   procedure P_Option (B : out Boolean; O : out Int_Option) with
     Depends => ((B, O) => O);

  procedure Call_P_Option (B_in : Boolean; B_out : out Boolean) with
     Depends => (B_out => B_in);
end;
