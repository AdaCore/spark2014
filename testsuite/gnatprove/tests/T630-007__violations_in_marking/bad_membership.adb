procedure Bad_Membership with SPARK_Mode is
   type Int_Acc is access Integer;
   type Option (Present : Boolean := False) is record
      case Present is
      when True  => Content : Int_Acc;
      when False => null;
      end case;
   end record;
   subtype None is Option (False);

   X : Option := (Present => True, Content => new Integer'(13));
begin
   pragma Assert (X in None | (Present => True, Content => new Integer'(13)));
   pragma Assert (X in (Present => True, Content => new Integer'(13)));
end Bad_Membership;
