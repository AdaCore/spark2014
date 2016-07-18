package body Aida.Strings.Generic_Immutable_Unbounded_String.Mutable is

   procedure Initialize (This : in out Mutable_T;
                         Text : String)
   is
      Temp : Positive := 1 with Ghost;
   begin
      Char_Vectors.Clear (This.Text);
      for I in Positive range Text'First..Text'Last loop
         Char_Vectors.Append (Container => This.Text,
                              New_Item  => Text (I));

         pragma Loop_Invariant (Positive (Length (This)) = Temp);
         pragma Loop_Invariant (Temp = I - Text'First + 1);
         Temp := (if Temp < Positive'Last then Temp + 1 else Positive'Last);
      end loop;
   end Initialize;

   procedure Append (This : in out Mutable_T;
                     Text : String) is
   begin
      for I in Positive range Text'First..Text'Last loop
         Char_Vectors.Append (Container => This.Text,
                              New_Item  => Text (I));
      end loop;
   end Append;

end Aida.Strings.Generic_Immutable_Unbounded_String.Mutable;
